/*  Copyright (C) 2014 CZ.NIC, z.s.p.o. <knot-dns@labs.nic.cz>

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

#include "libknot/dname.h"
#include "common/mem.h"
#include "common/namedb/namedb.h"
#include "common/namedb/namedb_lmdb.h"
#include "knot/zone/timers.h"
#include "knot/zone/zonedb.h"

/* ---- Knot-internal event code to db key lookup tables ------------------ - */

#define PERSISTENT_EVENT_COUNT 3

enum {
	KEY_REFRESH = 1,
	KEY_EXPIRE,
	KEY_FLUSH
};

// Do not change these mappings if you want backwards compatibility.
static const uint8_t event_id_to_key[ZONE_EVENT_COUNT] = {
 [ZONE_EVENT_REFRESH] = KEY_REFRESH,
 [ZONE_EVENT_EXPIRE] = KEY_EXPIRE,
 [ZONE_EVENT_FLUSH] = KEY_FLUSH
};

static const int key_to_event_id[PERSISTENT_EVENT_COUNT + 1] = {
 [KEY_REFRESH] = ZONE_EVENT_REFRESH,
 [KEY_EXPIRE] = ZONE_EVENT_EXPIRE,
 [KEY_FLUSH] = ZONE_EVENT_FLUSH
};

static bool known_event_key(uint8_t key)
{
	return key <= KEY_FLUSH;
}

#define EVENT_KEY_PAIR_SIZE (sizeof(uint8_t) + sizeof(int64_t))

static bool event_persistent(size_t event)
{
	return event_id_to_key[event] != 0;
}

/*! \brief Stores timers for persistent events. */
static int store_timers(knot_txn_t *txn, zone_t *zone)
{
	// Create key
	knot_val_t key = { .len = knot_dname_size(zone->name), .data = zone->name };
	
	// Create value
	uint8_t packed_timer[EVENT_KEY_PAIR_SIZE * PERSISTENT_EVENT_COUNT];
	size_t offset = 0;
	for (zone_event_type_t event = 0; event < ZONE_EVENT_COUNT; ++event) {
		if (!event_persistent(event)) {
			continue;
		}

		// Write event key and timer to buffer
		packed_timer[offset] = event_id_to_key[event];
		offset += 1;
		knot_wire_write_u64(packed_timer + offset,
		                    (int64_t)zone_events_get_time(zone, event));
		offset += sizeof(uint64_t);
	}
	knot_val_t val = { .len = sizeof(packed_timer), .data = packed_timer };

	// Store
	return namedb_lmdb_api()->insert(txn, &key, &val, 0);
}

/*! \brief Reads timers for persistent events. */
static int read_timers(knot_txn_t *txn, const zone_t *zone, time_t *timers)
{
	const struct namedb_api *db_api = namedb_lmdb_api();

	knot_val_t key = { .len = knot_dname_size(zone->name), .data = zone->name };
	knot_val_t val;
	int ret = db_api->find(txn, &key, &val, 0);
	if (ret != KNOT_EOK) {
		if (ret == KNOT_ENOENT) {
			// New zone, no entry in db.
			memset(timers, 0, ZONE_EVENT_COUNT * sizeof(time_t));
			return KNOT_EOK;
		}
		return ret;
	}

	// Set unknown/unset event timers to 0.
	memset(timers, 0, ZONE_EVENT_COUNT * sizeof(time_t));

	const size_t stored_event_count = val.len / EVENT_KEY_PAIR_SIZE;
	size_t offset = 0;
	for (size_t i = 0; i < stored_event_count; ++i) {
		const uint8_t db_key = ((uint8_t *)val.data)[offset];
		offset += 1;
		if (known_event_key(db_key)) {
			const zone_event_type_t event = key_to_event_id[db_key];
			timers[event] = (time_t)knot_wire_read_u64(val.data + offset);
		}
		offset += sizeof(uint64_t);
	}

	return KNOT_EOK;
}

/* -------- API ------------------------------------------------------------- */

knot_namedb_t *open_timers_db(const char *storage)
{
#ifndef HAVE_LMDB
	// No-op if we don't have lmdb, all other operations will no-op as well then
	return NULL;
#else
	char *path = sprintf_alloc("%s/timers", storage);
	if (!path) {
		return NULL;
	}

	knot_namedb_t *db = namedb_lmdb_api()->init(path, NULL);

	free(path);

	return db;
#endif
}

void close_timers_db(knot_namedb_t *timer_db)
{
	if (timer_db) {
		namedb_lmdb_api()->deinit(timer_db);
	}
}

int read_zone_timers(knot_namedb_t *timer_db, const zone_t *zone, time_t *timers)
{
	if (timer_db == NULL) {
		memset(timers, 0, ZONE_EVENT_COUNT * sizeof(time_t));
		return KNOT_EOK;
	}

	const struct namedb_api *db_api = namedb_lmdb_api();

	knot_txn_t txn;
	int ret = db_api->txn_begin(timer_db, &txn, KNOT_NAMEDB_RDONLY);
	if (ret != KNOT_EOK) {
		return ret;
	}

	ret = read_timers(&txn, zone, timers);
	db_api->txn_abort(&txn);
	if (ret != KNOT_EOK) {
		return ret;
	}

	return KNOT_EOK;
}

int write_zone_timers(knot_namedb_t *timer_db, zone_t *zone)
{
	if (timer_db == NULL) {
		return KNOT_EOK;
	}

	const struct namedb_api *db_api = namedb_lmdb_api();

	knot_txn_t txn;
	int ret = db_api->txn_begin(timer_db, &txn, 0);
	if (ret != KNOT_EOK) {
		return ret;
	}

	ret = store_timers(&txn, zone);
	if (ret != KNOT_EOK) {
		db_api->txn_abort(&txn);
		return ret;
	}

	return db_api->txn_commit(&txn);
}

int sweep_timer_db(knot_namedb_t *timer_db, knot_zonedb_t *zone_db)
{
	if (timer_db == NULL) {
		return KNOT_EOK;
	}
	const struct namedb_api *db_api = namedb_lmdb_api();

	knot_txn_t txn;
	int ret = db_api->txn_begin(timer_db, &txn, KNOT_NAMEDB_SORTED);
	if (ret != KNOT_EOK) {
		return ret;
	}

	if (db_api->count(&txn) == 0) {
		db_api->txn_abort(&txn);
		return KNOT_EOK;
	}

	knot_iter_t *it = db_api->iter_begin(&txn, 0);
	if (it == NULL) {
		db_api->txn_abort(&txn);
		return KNOT_ERROR;
	}

	while (it) {
		knot_val_t key;
		ret = db_api->iter_key(it, &key);
		if (ret != KNOT_EOK) {
			db_api->txn_abort(&txn);
			return ret;
		}
		const knot_dname_t *dbkey = (const knot_dname_t *)key.data;
		if (!knot_zonedb_find(zone_db, dbkey)) {
			// Delete obsolete timers
			db_api->del(&txn, &key);
		}

		it = db_api->iter_next(it);
	}
	db_api->iter_finish(it);

	return db_api->txn_commit(&txn);
}

