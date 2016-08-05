
#include <assert.h>
#include <stdlib.h>

#include <stdio.h> // XXX: just debug

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
    Tclear(trie);
}
size_t hattrie_weight(const hattrie_t *trie) {
    return Tweight(trie);
}


hattrie_t* hattrie_dup(const hattrie_t *trie, value_t (*nval)(value_t)) {
    return Tdup(trie, nval);
}

void hattrie_build_index(hattrie_t *trie) {
    // not needed
    UNUSED(trie);
}

int hattrie_apply_rev(hattrie_t *trie, int (*f)(value_t*,void*), void* d) {
    return Tapply(trie, f, d);
}
int hattrie_apply_rev_ahtable(hattrie_t *trie, int (*f)(void*,void*), void* d) {
    fprintf(stderr, "hattrie_apply_rev_ahtable\n");
    abort();
}


value_t* hattrie_tryget(hattrie_t *trie, const char *key, size_t len) {
    return Tget_try(trie, key, len);
}
value_t* hattrie_get(hattrie_t *trie, const char *key, size_t len) {
    return Tget_ins(trie, key, len);
}

int hattrie_find_next(hattrie_t *trie, const char *key, size_t len, value_t **dst) {
    abort(); // it's dead code, except for tests
    // beware: we update local parameters key and len in-place
    //return Tget_next(trie, &key, &len, dst) ? 1 : 0;
}
int hattrie_find_leq(hattrie_t *trie, const char *key, size_t len, value_t **dst) {
    return Tget_leq(trie, key, len, dst);
}

int hattrie_del(hattrie_t *trie, const char* key, size_t len) {
    return Tdel(trie, key, len, NULL) ? 0 : -1;
}


hattrie_iter_t* hattrie_iter_begin(const hattrie_t *trie, bool sorted) {
    UNUSED(sorted); // iteration over QP is always sorted ATM
    return Tit_begin(/*const-cast*/(hattrie_t*) trie);
}
void hattrie_iter_next(hattrie_iter_t *it) {
    Tit_next(it); // TODO: ignored OOM
}
bool hattrie_iter_finished(hattrie_iter_t *it) {
    return Tit_finished(it);
}
void hattrie_iter_free(hattrie_iter_t *it) {
    Tit_free(it);
}
const char* hattrie_iter_key (hattrie_iter_t *it, size_t *len) {
    return Tit_key(it, len);
}
value_t* hattrie_iter_val(hattrie_iter_t *it) {
    return Tit_val(it);
}

