/*  Copyright (C) 2018 CZ.NIC, z.s.p.o. <knot-dns@labs.nic.cz>

    This program is free software: you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.

    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */

#include "knot/include/module.h"
#include "libknot/libknot.h"
#include "contrib/qp-trie/trie.h"
#include "contrib/mempattern.h"
#include "knot/conf/conf.h"
#include "contrib/ucw/lists.h"
#include "contrib/sockaddr.h"
#include "contrib/openbsd/strlcpy.h"

// Next dependecies force static module!
#include "knot/dnssec/key-events.h"
#include "knot/dnssec/rrset-sign.h"
#include "knot/dnssec/zone-keys.h"
#include "knot/nameserver/query_module.h"

#include <stdio.h>
#include <string.h>
#include <arpa/inet.h>

#if HAVE_MAXMINDDB
#include <maxminddb.h>
#endif

#define MOD_GEO_CONF_FILE "\x0D""geo-conf-file"
#define MOD_TTL "\x03""ttl"
#define MOD_MODE "\x04""mode"
#define MOD_GEODB_FILE "\x0A""geodb-file"

// MaxMind DB related constants.
#define ISO_CODE_LEN 2

enum operation_mode {
	MODE_SUBNET,
	MODE_GEODB
};

static const knot_lookup_t modes[] = {
	{ MODE_SUBNET, "subnet" },
	{ MODE_GEODB, "geodb" },
	{ 0, NULL }
};

const yp_item_t geoip_conf[] = {
	{ MOD_GEO_CONF_FILE, YP_TSTR, YP_VSTR = { "/etc/knot/geo.conf"} },
	{ MOD_TTL,           YP_TINT, YP_VINT = { 0, UINT32_MAX, 3600, YP_STIME } },
	{ MOD_MODE,          YP_TOPT, YP_VOPT = { modes, MODE_SUBNET } },
	{ MOD_GEODB_FILE,    YP_TSTR, YP_VSTR = { "" } },
	{ NULL }
};

typedef struct {
	enum operation_mode mode;
	uint32_t ttl;
	knot_mm_t mm;
	trie_t *geo_trie;

	bool dnssec;
	zone_keyset_t keyset;
	kdnssec_ctx_t kctx;

#if HAVE_MAXMINDDB
	MMDB_s db;
#endif
} geoip_ctx_t;

typedef struct {
	uint16_t type;
	uint32_t ttl;
	knot_rdataset_t data;
	knot_rrset_t *rrsig;
} geo_trie_rrset_t;

typedef struct {
	uint8_t prefix;
	in_addr_t addr;
} subnet_t;

typedef struct {
	char country_iso[3];
	char *city;
	uint16_t city_len;
} geodata_t;

typedef struct {
	subnet_t subnet;
	geodata_t geodata;
	list_t rrsets;
} geo_trie_rrsets_t;

typedef struct {
	size_t arr_size;
	size_t arr_used;
	geo_trie_rrsets_t *arr;
} geo_trie_val_t;

static int add_ip_to_rrset(char *ip_str, knot_rdataset_t *rrs, knot_mm_t *mm)
{
	in_addr_t addr;
	int ret = KNOT_EOK;
	if (inet_pton(AF_INET, ip_str, &addr) == 1) {
		uint8_t buf[knot_rdata_size(sizeof(in_addr_t))];
		knot_rdata_t *rr = (knot_rdata_t *)buf;
		knot_rdata_init(rr, sizeof(in_addr_t), (uint8_t *)&addr);
		ret = knot_rdataset_add(rrs, rr, mm);
	} else {
		return KNOT_EMALF;
	}
	return ret;
}

static int add_rrset_to_trie(knot_dname_t *owner, knot_rdataset_t *rrs, knot_rrset_t *rrsig,
                             geoip_ctx_t *ctx, subnet_t subnet, geodata_t geodata)
{
	int ret = KNOT_EOK;

	// Create new rrset.
	geo_trie_rrset_t *new_rrset = mm_alloc(&ctx->mm, sizeof(geo_trie_rrset_t));
	new_rrset->type = KNOT_RRTYPE_A;
	new_rrset->ttl = ctx->ttl;
	ret = knot_rdataset_copy(&new_rrset->data, rrs, &ctx->mm);
	if (ret != KNOT_EOK) {
		return ret;
	}

	// Add RRSIG.
	if (rrsig != NULL) {
		new_rrset->rrsig = knot_rrset_copy(rrsig, &ctx->mm);
	}

	// Add the new rrset to trie.
	trie_val_t *val = trie_get_ins(ctx->geo_trie, (char *)owner, knot_dname_size(owner));
	geo_trie_val_t *cur_val = *val;
	if (cur_val == NULL) {
		// Create new node value.
		geo_trie_val_t *new_val = mm_calloc(&ctx->mm, 1, sizeof(geo_trie_val_t));
		new_val->arr_size = 1;
		new_val->arr_used = 1;
		new_val->arr = mm_alloc(&ctx->mm, sizeof(geo_trie_rrsets_t));
		new_val->arr[0].subnet = subnet;
		new_val->arr[0].geodata = geodata;

		// Create new list in the node.
		init_list(&new_val->arr[0].rrsets);
		ptrlist_add(&new_val->arr[0].rrsets, new_rrset, &ctx->mm);

		// Add new value to trie.
		*val = new_val;
	} else {
		// Double the rrsets array in size if necessary.
		if (cur_val->arr_used >= cur_val->arr_size) {
			void *alloc_ret = mm_realloc(&ctx->mm, cur_val->arr,
			                             2 * cur_val->arr_size * sizeof(geo_trie_rrsets_t),
			                             cur_val->arr_size * sizeof(geo_trie_rrsets_t));
			if (alloc_ret == NULL) {
				return KNOT_ENOMEM;
			}
			cur_val->arr = alloc_ret;
			cur_val->arr_size *= 2;
		}

		// Insert new element.
		cur_val->arr[cur_val->arr_used].subnet = subnet;
		cur_val->arr[cur_val->arr_used].geodata = geodata;
		init_list(&cur_val->arr[cur_val->arr_used].rrsets);
		ptrlist_add(&cur_val->arr[cur_val->arr_used].rrsets, new_rrset, &ctx->mm);
		cur_val->arr_used++;
	}

	return ret;
}

static bool addr_in_subnet(in_addr_t addr, subnet_t subnet)
{
	uint8_t mask_data[sizeof(in_addr_t)] = { 0 };
	for (int i = 0; i < subnet.prefix / 8; i++) {
		mask_data[i] = UINT8_MAX;
	}
	if (subnet.prefix % 8 != 0) {
		mask_data[subnet.prefix / 8] = ((1 << (subnet.prefix % 8)) - 1) << (8 - subnet.prefix % 8);
	}
	in_addr_t *mask = (in_addr_t *)mask_data;
	return (addr & *mask) == subnet.addr;
}

static bool addr_in_geo(knotd_mod_t *mod, const struct sockaddr *addr, geodata_t geodata)
{
#if HAVE_MAXMINDDB
	geoip_ctx_t *ctx = (geoip_ctx_t *)knotd_mod_ctx(mod);

	int mmdb_error = 0;
	MMDB_lookup_result_s res;
	res = MMDB_lookup_sockaddr(&ctx->db, addr, &mmdb_error);
	if (mmdb_error != MMDB_SUCCESS) {
		knotd_mod_log(mod, LOG_ERR, "a lookup error in MMDB occured");
		return false;
	}
	if (!res.found_entry) {
		return false;
	}

	geodata_t found;
	MMDB_entry_data_s entry;

	// Get remote country ISO code.
	mmdb_error = MMDB_get_value(&res.entry, &entry, "country", "iso_code", NULL);
	if (mmdb_error != MMDB_SUCCESS) {
		knotd_mod_log(mod, LOG_ERR, "an error in MMDB occured");
		return false;
	}
	if (!entry.has_data || entry.type != MMDB_DATA_TYPE_UTF8_STRING) {
		return false;
	}
	memcpy(found.country_iso, entry.utf8_string, entry.data_size);

	// Get remote city name.
	mmdb_error = MMDB_get_value(&res.entry, &entry, "city", "names", "en", NULL);
	if (mmdb_error != MMDB_SUCCESS) {
		knotd_mod_log(mod, LOG_ERR, "an error in MMDB occured");
		return false;
	}
	if (entry.has_data && entry.type == MMDB_DATA_TYPE_UTF8_STRING) {
		found.city_len = entry.data_size;
		found.city = mm_alloc(&ctx->mm, entry.data_size + 1);
		memcpy(found.city, entry.utf8_string, found.city_len);
	}
	else {
		found.city = NULL;
	}

	// Compare geodata.
	if (memcmp(geodata.country_iso, found.country_iso, ISO_CODE_LEN) != 0) {
		return false;
	}
	if (geodata.city == NULL) {
		return true;
	}
	if (found.city == NULL || found.city_len != geodata.city_len ||
	    memcmp(found.city, geodata.city, found.city_len) != 0) {
		return false;
	}
	return true;
#endif
	return false;
}

// Parsing helper for the time being.
#define MAX_TXT_SUBNET_LENGTH 18
#define MAX_TXT_IP_LENGTH 15

static int geo_conf_parse(knotd_mod_t *mod, geoip_ctx_t *ctx)
{
	knotd_conf_t conf = knotd_conf_mod(mod, MOD_GEO_CONF_FILE);
	const char *path = conf.single.string;
	FILE *f = fopen(path, "r");

	char owner_str[KNOT_DNAME_TXT_MAXLEN + 1];
	char subnet_str[MAX_TXT_SUBNET_LENGTH + 1];
	char ip_str[MAX_TXT_IP_LENGTH + 1];
	knot_dname_t owner[KNOT_DNAME_MAXLEN];
	char country_iso[3];
	char city[20];

	int rr_cnt, ret;

	while (1) {
		if (ctx->mode == MODE_SUBNET) {
			if (fscanf(f, "%s %s %d\n", owner_str, subnet_str, &rr_cnt) != 3) {
				break;
			}
		}
		if (ctx->mode == MODE_GEODB) {
			if (fscanf(f, "%s %s %s %d\n", owner_str, country_iso, city, &rr_cnt) != 4) {
				break;
			}
		}

		knot_rdataset_t rrs;
		knot_rdataset_init(&rrs);
		for (int i = 0; i < rr_cnt; i++) {
			fscanf(f, "%s", ip_str);

			ret = add_ip_to_rrset(ip_str, &rrs, &ctx->mm);
			if (ret != KNOT_EOK) {
				return ret;
			}
		}

		// Parse subnet string.
		subnet_t subnet = { 0 };
		if (ctx->mode == MODE_SUBNET) {
			char *slash = strchr(subnet_str, '/');
			subnet.prefix = atoi(slash + 1);
			*slash = '\0';
			inet_pton(AF_INET, subnet_str, &subnet.addr);
		}

		// Parse geodata.
		geodata_t geodata;
		if (ctx->mode == MODE_GEODB) {
			strlcpy(geodata.country_iso, country_iso, ISO_CODE_LEN + 1);
			if (city[0] == '*') {
				geodata.city_len = 0;
				geodata.city = NULL;
			} else {
				geodata.city_len = strlen(city);
				geodata.city = mm_alloc(&ctx->mm, geodata.city_len + 1);
				strlcpy(geodata.city, city, geodata.city_len + 1);
			}
		}

		// Parse owner string.
		(void)knot_dname_from_str(owner, owner_str, sizeof(owner));

		// Sign the rrset if DNSSEC is on.
		knot_rrset_t *rrsig = NULL;
		if (ctx->dnssec) {
			knot_rrset_t *rrset = knot_rrset_new(owner, KNOT_RRTYPE_A, KNOT_CLASS_IN, ctx->ttl, &ctx->mm);
			knot_rdataset_copy(&rrset->rrs, &rrs, &ctx->mm);
			rrsig = knot_rrset_new(owner, KNOT_RRTYPE_RRSIG, KNOT_CLASS_IN,
			                       ctx->ttl, &ctx->mm);
			for (size_t i = 0; i < ctx->keyset.count; i++) {
				zone_key_t *key = &ctx->keyset.keys[i];
				if (key->is_zsk) {
					knot_sign_rrset(rrsig, rrset, key->key, key->ctx, &ctx->kctx, &ctx->mm);
				}
			}
		}

		ret = add_rrset_to_trie(owner, &rrs, rrsig, ctx, subnet, geodata);
		if (ret != KNOT_EOK) {
			return ret;
		}
	}

	fclose(f);

	return KNOT_EOK;
}

#define SEND_RRSET() \
geo_trie_rrset_t *head = (geo_trie_rrset_t *)((ptrnode_t *)HEAD(data->arr[i].rrsets))->d; \
knot_rrset_t out_rrset; \
knot_rrset_init(&out_rrset, qname, head->type, knot_pkt_qclass(qdata->query), head->ttl); \
knot_rdataset_copy(&out_rrset.rrs, &head->data, &ctx->mm); \
knot_pkt_put(pkt, KNOT_COMPR_HINT_QNAME, &out_rrset, 0); \
if (ctx->dnssec && knot_pkt_has_dnssec(qdata->query)) { \
	knot_pkt_put(pkt, KNOT_COMPR_HINT_QNAME, head->rrsig, 0); \
} \
return KNOTD_IN_STATE_HIT;

static knotd_in_state_t geoip_process(knotd_in_state_t state, knot_pkt_t *pkt,
                                   knotd_qdata_t *qdata, knotd_mod_t *mod)
{
	assert(pkt && qdata && mod);

	geoip_ctx_t *ctx = (geoip_ctx_t *)knotd_mod_ctx(mod);

	// Geolocate only A or AAAA records.
	uint16_t qtype = knot_pkt_qtype(qdata->query);
	if (qtype != KNOT_RRTYPE_A && qtype != KNOT_RRTYPE_AAAA) {
		return state;
	}

	// Check if geolocation is available for given query.
	knot_dname_t *qname = knot_pkt_qname(qdata->query);
	size_t qname_len = knot_dname_size(qname);
	trie_val_t *val = trie_get_try(ctx->geo_trie, (char *)qname, qname_len);
	if (val == NULL) {
		// Nothing to do in this module.
		return state;
	}

	geo_trie_val_t *data = *val;

	if (ctx->mode == MODE_SUBNET) {
		in_addr_t remote = ((struct sockaddr_in *)qdata->params->remote)->sin_addr.s_addr;

		// Check whether the remote falls into any geo subnet.
		for (int i = 0; i < data->arr_used; i++) {
			if (addr_in_subnet(remote, data->arr[i].subnet)) {
				SEND_RRSET();
			}
		}
	}

	if (ctx->mode == MODE_GEODB) {
		// Check whether the remote falls into any geo location.
		for (int i = 0; i < data->arr_used; i++) {
			if (addr_in_geo(mod, (const struct sockaddr *)qdata->params->remote, data->arr[i].geodata)) {
				SEND_RRSET();
			}
		}
	}

	// Dump found rrsets for debug reasons.
	/* for (int i = 0; i < data->arr_used; i++) {
		geo_trie_rrset_t *head = (geo_trie_rrset_t *)((ptrnode_t *)HEAD(data->arr[i].rrsets))->d;
		knot_rrset_t out_rrset;
		knot_rrset_init(&out_rrset, qname, head->type, knot_pkt_qclass(qdata->query), head->ttl);
		knot_rdataset_copy(&out_rrset.rrs, &head->data, &ctx->mm);
		size_t dump_size = 1024;
		char *txt_dump = malloc(dump_size);
		printf("subnet %.04x/%u\n", data->arr[i].subnet.addr, data->arr[i].subnet.prefix);
		printf("%s\n", (addr_in_subnet(((struct sockaddr_in *)qdata->params->remote)->sin_addr.s_addr, data->arr[i].subnet)) ? "yes" : "no");
		knot_rrset_txt_dump(&out_rrset, &txt_dump, &dump_size, &KNOT_DUMP_STYLE_DEFAULT);
		printf("%s", txt_dump);
		free(txt_dump);
	} */

	return state;
}

int geoip_load(knotd_mod_t *mod)
{
	// Create module context.
	geoip_ctx_t *ctx = calloc(1, sizeof(geoip_ctx_t));
	if (ctx == NULL) {
		return KNOT_ENOMEM;
	}

	knotd_conf_t conf = knotd_conf_mod(mod, MOD_TTL);
	ctx->ttl = conf.single.integer;
	conf = knotd_conf_mod(mod, MOD_MODE);
	ctx->mode = conf.single.option;

	// Initialize memory context
	mm_ctx_mempool(&ctx->mm, MM_DEFAULT_BLKSIZE);
	// Initialize the dname trie
	ctx->geo_trie = trie_create(&ctx->mm);

	int ret;

	// Initialize geodb if configured.
#if HAVE_MAXMINDDB
	if (ctx->mode == MODE_GEODB) {
		conf = knotd_conf_mod(mod, MOD_GEODB_FILE);
		ret = MMDB_open(conf.single.string, MMDB_MODE_MMAP, &ctx->db);
		if (ret != MMDB_SUCCESS) {
			knotd_mod_log(mod, LOG_ERR, "failed to open Geo DB");
			return KNOT_EINVAL;
		}
	}
#endif

	// Is DNSSEC used on this zone?
	conf = knotd_conf_zone(mod, C_DNSSEC_SIGNING, knotd_mod_zone(mod));
	ctx->dnssec = conf.single.boolean;
	if (ctx->dnssec) {
		ret = kdnssec_ctx_init(mod->config, &ctx->kctx, mod->zone, NULL);
		if (ret != KNOT_EOK) {
			kdnssec_ctx_deinit(&ctx->kctx);
			free(ctx);
			return ret;
		}
		ret = load_zone_keys(&ctx->kctx, &ctx->keyset, true);
		if (ret != KNOT_EOK) {
			knotd_mod_log(mod, LOG_ERR, "failed to load keys");
			kdnssec_ctx_deinit(&ctx->kctx);
			free(ctx);
			return ret;
		}
	}

	// Parse geo configuration file
	ret = geo_conf_parse(mod, ctx);
	if (ret != KNOT_EOK) {
		knotd_mod_log(mod, LOG_ERR, "failed to load geo configuration");
		free(ctx);
		return ret;
	}

	knotd_mod_ctx_set(mod, ctx);

	return knotd_mod_in_hook(mod, KNOTD_STAGE_PREANSWER, geoip_process);
}

void geoip_unload(knotd_mod_t *mod)
{
	geoip_ctx_t *ctx = knotd_mod_ctx(mod);
	if (ctx != NULL) {
		kdnssec_ctx_deinit(&ctx->kctx);
		free_zone_keys(&ctx->keyset);
#if HAVE_MAXMINDDB
		MMDB_close(&ctx->db);
#endif
	}
	free(ctx);
	assert(mod);
}

KNOTD_MOD_API(geoip, KNOTD_MOD_FLAG_SCOPE_ZONE | KNOTD_MOD_FLAG_OPT_CONF,
              geoip_load, geoip_unload, geoip_conf, NULL);
