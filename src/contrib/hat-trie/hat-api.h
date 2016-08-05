
#pragma once

#include <stdbool.h>
#include <stddef.h>

#include "libknot/mm_ctx.h"

typedef void* value_t;
/* API notes:
 *  - any key passed shouldn't be kept by the structure (it should make a deep copy)
 */

hattrie_t* hattrie_create (void);              //< Create an empty hat-trie.
void       hattrie_free   (hattrie_t*);        //< Free all memory used by a trie.
void       hattrie_clear  (hattrie_t*);        //< Remove all entries.
size_t     hattrie_weight (const hattrie_t*);  //< Number of entries

/** Create new trie with custom bucket size and memory management.
 */
hattrie_t* hattrie_create_n (unsigned, const struct knot_mm *);

/** Duplicate an existing trie.
 *
 *  If nval == NULL, make the new trie empty (but copy mm).
 */
hattrie_t* hattrie_dup (const hattrie_t*, value_t (*nval)(value_t));

/** Build order index on all ahtable nodes in trie.
 */
void hattrie_build_index (hattrie_t*);

/** Apply a function to each node, in order. */
int hattrie_apply_rev (hattrie_t*, int (*f)(value_t*,void*), void* d);
/** Apply a function to each hash-table node (!), in order. */
int hattrie_apply_rev_ahtable(hattrie_t* T, int (*f)(void*,void*), void* d);

/** Find the given key in the trie, inserting it if it does not exist, and
 * returning a pointer to its key.
 *
 * This pointer is not guaranteed to be valid after additional calls to
 * hattrie_get, hattrie_del, hattrie_clear, or other functions that modifies the
 * trie.
 */
value_t* hattrie_get (hattrie_t*, const char* key, size_t len);

/** Find a given key in the table, returning a NULL pointer if it does not
 * exist. */
value_t* hattrie_tryget (hattrie_t*, const char* key, size_t len);

/** Find a given key in the table, returning a NULL pointer if it does not
 * exist. Note: dst must be valid.
 * Return 0 for exact match, -1 for previous, 1 for not-found. */
int hattrie_find_leq (hattrie_t*, const char* key, size_t len, value_t** dst);
/** Find a next value for given key, setting NULL if it does not exist.
 *  Returns 1 or 0. Basially unused. */
int hattrie_find_next (hattrie_t* T, const char* key, size_t len, value_t **dst);

/** Delete a given key from trie. Returns 0 if successful or -1 if not found.
 */
int hattrie_del(hattrie_t* T, const char* key, size_t len);

/** Create a new iterator, "pointing" at the "first" element. */
hattrie_iter_t* hattrie_iter_begin     (const hattrie_t*, bool sorted);
void            hattrie_iter_next      (hattrie_iter_t*);
/** Check if the iterator has gone past the "last" element. */
bool            hattrie_iter_finished  (hattrie_iter_t*);
void            hattrie_iter_free      (hattrie_iter_t*);
const char*     hattrie_iter_key       (hattrie_iter_t*, size_t* len);
value_t*        hattrie_iter_val       (hattrie_iter_t*);

