
#include <assert.h>
#include <stdlib.h>

typedef struct Tbl hattrie_t;
#include "contrib/hat-trie/hat-api.h"

#include "contrib/qp-trie/qp.h"
#include "contrib/macros.h"

// FIXME: unimplemented stuff with abort()


hattrie_t* hattrie_create(void) { //< Create an empty hat-trie.
    return Tcreate(NULL);
}
hattrie_t* hattrie_create_n(unsigned bucket_size, const struct knot_mm *mm) {
    UNUSED(bucket_size);
    return Tcreate(/*const-cast*/(struct knot_mm*) mm);
}
void hattrie_free(hattrie_t *trie) {
    Tfree(trie);
}
void hattrie_clear(hattrie_t *trie) {
    abort();
}
size_t hattrie_weight(const hattrie_t *trie) {
    return Tweight(trie);
}


hattrie_t* hattrie_dup(const hattrie_t *trie, value_t (*nval)(value_t)) {
    abort();
}

void hattrie_build_index(hattrie_t *trie) {
    // not needed
}

int hattrie_apply_rev(hattrie_t *trie, int (*f)(value_t*,void*), void* d) {
    abort();
}
int hattrie_apply_rev_ahtable(hattrie_t *trie, int (*f)(void*,void*), void* d) {
    abort();
}


value_t* hattrie_tryget(hattrie_t *trie, const char *key, size_t len) {
    return Tget_try(trie, key, len);
}
value_t* hattrie_get(hattrie_t *trie, const char *key, size_t len) {
    return Tget_ins(trie, key, len);
}

int hattrie_find_next(hattrie_t *trie, const char *key, size_t len, value_t **dst) {
    // beware: we update local parameters key and len in-place
    bool found = Tget_next(trie, &key, &len, dst);
    return found ? 1 : 0;
}
int hattrie_find_leq(hattrie_t *trie, const char *key, size_t len, value_t **dst) {
}

int hattrie_del(hattrie_t* T, const char* key, size_t len);

typedef struct hattrie_iter_t_ hattrie_iter_t;

hattrie_iter_t* hattrie_iter_begin     (const hattrie_t*, bool sorted);
void            hattrie_iter_next      (hattrie_iter_t*);
bool            hattrie_iter_finished  (hattrie_iter_t*);
void            hattrie_iter_free      (hattrie_iter_t*);
const char*     hattrie_iter_key       (hattrie_iter_t*, size_t* len);
value_t*        hattrie_iter_val       (hattrie_iter_t*);
