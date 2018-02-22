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

#include <assert.h>

#include "libknot/attribute.h"
#include "libknot/consts.h"
#include "libknot/descriptor.h"
#include "libknot/packet/pkt.h"
#include "libknot/packet/rrset-wire.h"
#include "libknot/rrtype/naptr.h"
#include "libknot/rrtype/rrsig.h"
#include "contrib/macros.h"
#include "contrib/mempattern.h"
#include "contrib/tolower.h"
#include "contrib/wire_ctx.h"

/*!
 * \brief Get maximal size of a domain name in a wire with given capacity.
 */
static uint16_t dname_max(size_t wire_avail)
{
	return MIN(wire_avail, KNOT_DNAME_MAXLEN);
}

/*!
 * \brief Compares two domain name labels.
 *
 * \param label1  First label.
 * \param label2  Second label (may be in upper-case).
 *
 * \retval true if the labels are identical
 * \retval false if the labels are NOT identical
 */
static bool label_is_equal(const uint8_t *label1, const uint8_t *label2)
{
	assert(label1 && label2);

	if (*label1 != *label2) {
		return false;
	}

	uint8_t len = *label1;
	for (uint8_t i = 1; i <= len; i++) {
		if (label1[i] != knot_tolower(label2[i])) {
			return false;
		}
	}

	return true;
}

/*!
 * Case insensitive comparison of two dnames in wire format.
 * The second name may be compressed in a supplied wire.
 */
static bool dname_equal_wire(const knot_dname_t *d1, const knot_dname_t *d2,
                             const uint8_t *wire)
{
	assert(d1);
	assert(d2);

	d2 = knot_wire_seek_label(d2, wire);

	while (*d1 != '\0' || *d2 != '\0') {
		if (!label_is_equal(d1, d2)) {
			return false;
		}
		d1 = knot_wire_next_label(d1, NULL);
		d2 = knot_wire_next_label(d2, wire);
	}

	return true;
}

/*!
 * \brief Get compression pointer for a given hint.
 */
static uint16_t compr_get_ptr(knot_compr_t *compr, uint16_t hint)
{
	if (compr == NULL) {
		return 0;
	}

	return knot_compr_hint(compr->rrinfo, hint);
}

/*!
 * \brief Set compression pointer for a given hint.
 */
static void compr_set_ptr(knot_compr_t *compr, uint16_t hint,
                          const uint8_t *written_at, uint16_t written_size)
{
	if (compr == NULL) {
		return;
	}

	assert(written_at >= compr->wire);

	uint16_t offset = written_at - compr->wire;

	knot_compr_hint_set(compr->rrinfo, hint, offset, written_size);
}

/*! \brief Helper for \ref compr_put_dname, writes label(s) with size checks. */
#define WRITE_LABEL(dst, written, label, max, len) \
	if ((written) + (len) > (max)) { \
		return KNOT_ESPACE; \
	} else { \
		memcpy((dst) + (written), (label), (len)); \
		written += (len); \
	}

/*!
 * \brief Write compressed domain name to the destination wire.
 *
 * \param dname Name to be written.
 * \param dst Destination wire.
 * \param max Maximum number of bytes available.
 * \param compr Compression context (NULL for no compression)
 * \return Number of written bytes or an error.
 */
static int compr_put_dname(const knot_dname_t *dname, uint8_t *dst, uint16_t max,
                           knot_compr_t *compr)
{
	assert(dname && dst);

	/* Write uncompressible names directly (zero label dname). */
	if (compr == NULL || *dname == '\0') {
		return knot_dname_to_wire(dst, dname, max);
	}

	/* Get number of labels (should not be a zero label dname). */
	size_t name_labels = knot_dname_labels(dname, NULL);
	assert(name_labels > 0);

	/* Suffix must not be longer than whole name. */
	const knot_dname_t *suffix = compr->wire + compr->suffix.pos;
	int suffix_labels = compr->suffix.labels;
	while (suffix_labels > name_labels) {
		suffix = knot_wire_next_label(suffix, compr->wire);
		--suffix_labels;
	}

	/* Suffix is shorter than name, write labels until aligned. */
	uint8_t orig_labels = name_labels;
	uint16_t written = 0;
	while (name_labels > suffix_labels) {
		WRITE_LABEL(dst, written, dname, max, (*dname + 1));
		dname = knot_wire_next_label(dname, NULL);
		--name_labels;
	}

	/* Label count is now equal. */
	assert(name_labels == suffix_labels);
	const knot_dname_t *match_begin = dname;
	const knot_dname_t *compr_ptr = suffix;
	while (dname[0] != '\0') {

		/* Next labels. */
		const knot_dname_t *next_dname = knot_wire_next_label(dname, NULL);
		const knot_dname_t *next_suffix = knot_wire_next_label(suffix, compr->wire);

		/* Two labels match, extend suffix length. */
		if (!label_is_equal(dname, suffix)) {
			/* If they don't match, write unmatched labels. */
			uint16_t mismatch_len = (dname - match_begin) + (*dname + 1);
			WRITE_LABEL(dst, written, match_begin, max, mismatch_len);
			/* Start new potential match. */
			match_begin = next_dname;
			compr_ptr = next_suffix;
		}

		/* Jump to next labels. */
		dname = next_dname;
		suffix = next_suffix;
	}

	/* If match begins at the end of the name, write '\0' label. */
	if (match_begin == dname) {
		WRITE_LABEL(dst, written, dname, max, 1);
	} else {
		/* Match covers >0 labels, write out compression pointer. */
		if (written + sizeof(uint16_t) > max) {
			return KNOT_ESPACE;
		}
		knot_wire_put_pointer(dst + written, compr_ptr - compr->wire);
		written += sizeof(uint16_t);
	}

	assert(dst >= compr->wire);
	size_t wire_pos = dst - compr->wire;
	assert(wire_pos < KNOT_WIRE_MAX_PKTSIZE);

	/* Heuristics - expect similar names are grouped together. */
	if (written > sizeof(uint16_t) && wire_pos + written < KNOT_WIRE_PTR_MAX) {
		compr->suffix.pos = wire_pos;
		compr->suffix.labels = orig_labels;
	}

	return written;
}

typedef struct {
	bool to_wire;
	knot_compr_t *compr;
	uint16_t hint;
	const uint8_t *pkt_wire;
} traverse_ctx_t;

static int compress_rdata_dname(wire_ctx_t *src, wire_ctx_t *dst, traverse_ctx_t *ctx,
                                int dname_type)
{
	assert(ctx);

	// Source domain name.
	const knot_dname_t *dname = src->position;
	size_t dname_size = knot_dname_size(dname);

	// Output domain name.
	knot_compr_t *put_compr = NULL;
	if (dname_type == KNOT_RDATA_WF_COMPRESSIBLE_DNAME) {
		put_compr = ctx->compr;
	}

	int written = compr_put_dname(dname, dst->position,
	                              dname_max(wire_ctx_available(dst)), put_compr);
	if (written < 0) {
		return written;
	}

	// Update compression hints.
	if (compr_get_ptr(ctx->compr, ctx->hint) == 0) {
		compr_set_ptr(ctx->compr, ctx->hint, dst->position, written);
	}

	wire_ctx_skip(src, dname_size);
	wire_ctx_skip(dst, written);
	assert(src->error == KNOT_EOK);
	assert(dst->error == KNOT_EOK);

	return KNOT_EOK;
}

static int decompress_rdata_dname(wire_ctx_t *src, wire_ctx_t *dst, traverse_ctx_t *ctx)
{
	assert(ctx);

	int compr_size = knot_dname_wire_check(src->position,
	                                       src->position + wire_ctx_available(src),
	                                       ctx->pkt_wire);
	if (compr_size <= 0) {
		return compr_size;
	}

	int decompr_size = knot_dname_unpack(dst->position, src->position,
	                                     wire_ctx_available(dst), ctx->pkt_wire);
	if (decompr_size <= 0) {
		return decompr_size;
	}

	wire_ctx_skip(src, compr_size);
	wire_ctx_skip(dst, decompr_size);
	assert(src->error == KNOT_EOK);
	assert(dst->error == KNOT_EOK);

	return KNOT_EOK;
}

static int write_rdata_fixed(wire_ctx_t *src, wire_ctx_t *dst, size_t size)
{
	if (wire_ctx_available(src) < size || wire_ctx_available(dst) < size) {
		return KNOT_ESPACE;
	}
	wire_ctx_write(dst, src->position, size);
	wire_ctx_skip(src, size);

	return dst->error;
}

static int write_rdata_naptr_header(wire_ctx_t *src, wire_ctx_t *dst)
{
	int ret = knot_naptr_header_size(src->position,
	                                 src->position + wire_ctx_available(src));
	if (ret < 0) {
		return ret;
	}

	return write_rdata_fixed(src, dst, ret);
}

static int write_rdata_block(int type, wire_ctx_t *src, wire_ctx_t *dst,
                             traverse_ctx_t *ctx)
{
	switch (type) {
	case KNOT_RDATA_WF_COMPRESSIBLE_DNAME:
	case KNOT_RDATA_WF_DECOMPRESSIBLE_DNAME:
	case KNOT_RDATA_WF_FIXED_DNAME:
		if (ctx->to_wire) {
			return compress_rdata_dname(src, dst, ctx, type);
		} else {
			return decompress_rdata_dname(src, dst, ctx);
		}
	case KNOT_RDATA_WF_NAPTR_HEADER:
		return write_rdata_naptr_header(src, dst);
	case KNOT_RDATA_WF_REMAINDER:
		return write_rdata_fixed(src, dst, wire_ctx_available(src));
	default:
		// Fixed size block.
		assert(type > 0);
		return write_rdata_fixed(src, dst, type);
	}
}

static int desc_traverse(const knot_rdata_descriptor_t *desc, wire_ctx_t *src,
                         wire_ctx_t *dst, traverse_ctx_t *ctx)
{
	for (const int *type = desc->block_types; *type != KNOT_RDATA_WF_END; type++) {
		int ret = write_rdata_block(*type, src, dst, ctx);
		if (ret != KNOT_EOK) {
			return ret;
		}
	}

	return KNOT_EOK;
}

#define WRITE_OWNER_CHECK(dst, size) \
	if (wire_ctx_available((dst)) < (size)) { \
		return KNOT_ESPACE; \
	}

#define WRITE_OWNER_RETURN(dst, size) \
	wire_ctx_skip((dst), (size)); \
	return dst->error;

static int write_owner(const knot_rrset_t *rrset, wire_ctx_t *dst, knot_compr_t *compr)
{
	assert(rrset);
	assert(dst);

	uint16_t owner_pointer = 0;
	if (*rrset->owner != '\0') {
		owner_pointer = compr_get_ptr(compr, KNOT_COMPR_HINT_OWNER);
	}

	// Check for zero label owner (don't compress).
	if (owner_pointer > 0) {
		WRITE_OWNER_CHECK(dst, sizeof(uint16_t));
		knot_wire_put_pointer(dst->position, owner_pointer);
		WRITE_OWNER_RETURN(dst, sizeof(uint16_t));
	// Check for coincidence with previous RR set.
	} else if (compr != NULL && compr->suffix.pos != 0 && *rrset->owner != '\0' &&
	           dname_equal_wire(rrset->owner, compr->wire + compr->suffix.pos,
	                            compr->wire)) {
		WRITE_OWNER_CHECK(dst, sizeof(uint16_t));
		knot_wire_put_pointer(dst->position, compr->suffix.pos);
		compr_set_ptr(compr, KNOT_COMPR_HINT_OWNER,
		              compr->wire + compr->suffix.pos,
		              knot_dname_size(rrset->owner));
		WRITE_OWNER_RETURN(dst, sizeof(uint16_t));
	} else {
		if (compr != NULL) {
			compr->suffix.pos = KNOT_WIRE_HEADER_SIZE;
			compr->suffix.labels =
				knot_dname_labels(compr->wire + compr->suffix.pos,
				                  compr->wire);
		}
		// WRITE_OWNER_CHECK not needed here.
		int written = compr_put_dname(rrset->owner, dst->position,
		                              dname_max(wire_ctx_available(dst)), compr);
		if (written < 0) {
			return written;
		}
		compr_set_ptr(compr, KNOT_COMPR_HINT_OWNER, dst->position, written);
		WRITE_OWNER_RETURN(dst, written);
	}
}

static int write_fixed_header(const knot_rrset_t *rrset, uint16_t rrset_index,
                              wire_ctx_t *dst)
{
	assert(rrset);
	assert(rrset_index < rrset->rrs.rr_count);
	assert(dst);

	wire_ctx_write_u16(dst, rrset->type);
	wire_ctx_write_u16(dst, rrset->rclass);

	if (rrset->type == KNOT_RRTYPE_RRSIG) {
		wire_ctx_write_u32(dst, knot_rrsig_original_ttl(&rrset->rrs, rrset_index));
	} else {
		wire_ctx_write_u32(dst, rrset->ttl);
	}

	return dst->error;
}

static int write_rdata(const knot_rrset_t *rrset, uint16_t rrset_index,
                       wire_ctx_t *dst, knot_compr_t *compr)
{
	assert(rrset);
	assert(rrset_index < rrset->rrs.rr_count);
	assert(dst);

	// Prepare room for rdata length.
	uint8_t *wire_rdlength = dst->position;
	wire_ctx_skip(dst, sizeof(uint16_t));
	if (dst->error != KNOT_EOK) {
		return dst->error;
	}

	const knot_rdata_t *rdata = knot_rdataset_at(&rrset->rrs, rrset_index);
	wire_ctx_t src = wire_ctx_init_const(rdata->data, rdata->len);

	// Only write non-empty data.
	if (wire_ctx_available(&src) > 0) {
		traverse_ctx_t ctx = {
			.to_wire = true,
			.compr = compr,
			.hint = KNOT_COMPR_HINT_RDATA + rrset_index
		};

		int ret = desc_traverse(knot_get_rdata_descriptor(rrset->type),
		                        &src, dst, &ctx);
		if (ret != KNOT_EOK) {
			return ret;
		}

		// Check for trailing data.
		if (wire_ctx_available(&src) > 0) {
			return KNOT_EMALF;
		}
	}

	// Write final rdata length.
	assert(dst->position > wire_rdlength);
	knot_wire_write_u16(wire_rdlength, dst->position - wire_rdlength - sizeof(uint16_t));

	return dst->error;
}

static int write_rr(const knot_rrset_t *rrset, uint16_t rrset_index,
                    wire_ctx_t *dst, knot_compr_t *compr)
{
	int ret = write_owner(rrset, dst, compr);
	if (ret != KNOT_EOK) {
		return ret;
	}

	ret = write_fixed_header(rrset, rrset_index, dst);
	if (ret != KNOT_EOK) {
		return ret;
	}

	return write_rdata(rrset, rrset_index, dst, compr);
}

_public_
int knot_rrset_to_wire(const knot_rrset_t *rrset, uint8_t *wire, uint16_t max_size,
                       knot_compr_t *compr)
{
	if (rrset == NULL || wire == NULL) {
		return KNOT_EINVAL;
	}

	wire_ctx_t dst = wire_ctx_init(wire, max_size);

	for (uint16_t i = 0; i < rrset->rrs.rr_count; i++) {
		int ret = write_rr(rrset, i, &dst, compr);
		if (ret != KNOT_EOK) {
			return ret;
		}
	}

	return wire_ctx_offset(&dst);
}

static int parse_header(const uint8_t *wire, wire_ctx_t *src, knot_rrset_t *rrset,
                        uint16_t *rdlen, knot_mm_t *mm)
{
	assert(wire);
	assert(src);
	assert(rrset);
	assert(rdlen);

	int compr_size = knot_dname_wire_check(src->position,
	                                       src->position + wire_ctx_available(src),
	                                       wire);
	if (compr_size <= 0) {
		return compr_size;
	}

	size_t decompr_size = knot_dname_realsize(src->position, wire);
	if (decompr_size == 0) {
		return KNOT_EMALF;
	}

	knot_dname_t *owner = mm_alloc(mm, decompr_size);
	if (owner == NULL) {
		return KNOT_ENOMEM;
	}

	int ret = knot_dname_unpack(owner, src->position, decompr_size, wire);
	if (ret < 0) {
		return ret;
	}
	assert(ret == decompr_size);
	wire_ctx_skip(src, compr_size);

	uint16_t type = wire_ctx_read_u16(src);
	uint16_t rclass = wire_ctx_read_u16(src);
	uint32_t ttl = wire_ctx_read_u32(src);
	*rdlen = wire_ctx_read_u16(src);

	if (src->error != KNOT_EOK) {
		knot_dname_free(owner, mm);
		return src->error;
	}

	knot_rrset_init(rrset, owner, type, rclass, ttl);

	return KNOT_EOK;
}

static bool allow_zero_rdata(const knot_rrset_t *rr,
                             const knot_rdata_descriptor_t *desc)
{
	return rr->rclass != KNOT_CLASS_IN ||  // NONE and ANY for DDNS
	       rr->type == KNOT_RRTYPE_APL ||  // APL RR type
	       desc->type_name == NULL;        // Unknown RR type
}

static int parse_rdata(const uint8_t *wire, wire_ctx_t *src, knot_rrset_t *rrset,
                       uint16_t rdlength, knot_mm_t *mm)
{
	assert(wire);
	assert(src);
	assert(rrset);

	const knot_rdata_descriptor_t *desc = knot_get_rdata_descriptor(rrset->type);
	if (desc->type_name == NULL) {
		desc = knot_get_obsolete_rdata_descriptor(rrset->type);
	}

	if (rdlength == 0) {
		if (allow_zero_rdata(rrset, desc)) {
			return knot_rrset_add_rdata(rrset, NULL, 0, mm);
		} else {
			return KNOT_EMALF;
		}
	}

	if (wire_ctx_available(src) < rdlength) {
		return KNOT_EMALF;
	}

	// Buffer for parsed rdata (decompression extends rdata length).
	const size_t max_rdata_len = MIN((size_t)rdlength +
	                                 KNOT_MAX_RDATA_DNAMES * KNOT_DNAME_MAXLEN,
	                                 UINT16_MAX);
	uint8_t buf[knot_rdata_size(max_rdata_len)];
	knot_rdata_t *rdata = (knot_rdata_t *)buf;

	wire_ctx_t dst = wire_ctx_init(rdata->data, max_rdata_len);

	// Parse RDATA.
	traverse_ctx_t ctx = {
		.to_wire = false,
		.pkt_wire = wire
	};

	int ret = desc_traverse(desc, src, &dst, &ctx);
	if (ret != KNOT_EOK) {
		return ret;
	}

	rdata->len = wire_ctx_offset(&dst);

	// Check for trailing data.
	if (rdata->len < rdlength) {
		return KNOT_EMALF;
	}

	ret = knot_rdataset_add(&rrset->rrs, rdata, mm);
	if (ret != KNOT_EOK) {
		return ret;
	}

	return src->error;
}

_public_
int knot_rrset_rr_from_wire(const uint8_t *wire, size_t *pos, size_t max_size,
                            knot_rrset_t *rrset, knot_mm_t *mm, bool canonical)
{
	if (wire == NULL || pos == NULL || *pos > max_size || rrset == NULL) {
		return KNOT_EINVAL;
	}

	wire_ctx_t src = wire_ctx_init_const(wire + *pos, max_size - *pos);

	uint16_t rdlen = 0;
	int ret = parse_header(wire, &src, rrset, &rdlen, mm);
	if (ret != KNOT_EOK) {
		return ret;
	}

	ret = parse_rdata(wire, &src, rrset, rdlen, mm);
	if (ret != KNOT_EOK) {
		knot_rrset_clear(rrset, mm);
		return ret;
	}

	assert(src.error == KNOT_EOK);
	*pos += wire_ctx_offset(&src);

	// Convert RR to the canonical format.
	if (canonical) {
		ret = knot_rrset_rr_to_canonical(rrset);
		if (ret != KNOT_EOK) {
			knot_rrset_clear(rrset, mm);
		}
	}

	return KNOT_EOK;
}
