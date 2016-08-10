
#include <assert.h>
#include <stdlib.h>

#include <stdio.h> // XXX: just debug

typedef struct qp_trie hattrie_t; // define again, to be sure we didn't mix it up
#include "contrib/hat-trie/hat-api.h"

#include "contrib/qp-trie/qp.h"
#include "contrib/macros.h"

// FIXME: unimplemented stuff with abort()


hattrie_t* hattrie_create(void)
{
    return qp_trie_create(NULL);
}
hattrie_t* hattrie_create_n(unsigned bucket_size, const struct knot_mm *mm)
{
    UNUSED(bucket_size);
    return qp_trie_create(/*const-cast*/(struct knot_mm*)mm);
}
void hattrie_free(hattrie_t *trie)
{
    qp_trie_free(trie);
}
void hattrie_clear(hattrie_t *trie)
{
    qp_trie_clear(trie);
}
size_t hattrie_weight(const hattrie_t *trie)
{
    return qp_trie_weight(trie);
}


hattrie_t* hattrie_dup(const hattrie_t *trie, value_t (*nval)(value_t))
{
    return qp_trie_dup(trie, nval);
}

void hattrie_build_index(hattrie_t *trie)
{
    // not needed
    UNUSED(trie);
}

int hattrie_apply_rev(hattrie_t *trie, int (*f)(value_t*,void*), void* d)
{
    return qp_trie_apply(trie, f, d);
}


value_t* hattrie_tryget(hattrie_t *trie, const char *key, size_t len)
{
    return qp_trie_get_try(trie, key, len);
}
value_t* hattrie_get(hattrie_t *trie, const char *key, size_t len)
{
    return qp_trie_get_ins(trie, key, len);
}

int hattrie_find_next(hattrie_t *trie, const char *key, size_t len, value_t **dst)
{
    fprintf(stderr, "hattrie_find_next\n");
    abort(); // it's dead code, except for tests
    // beware: we update local parameters key and len in-place
    //return qp_trie_get_next(trie, &key, &len, dst) ? 1 : 0;
}
int hattrie_find_leq(hattrie_t *trie, const char *key, size_t len, value_t **dst)
{
    return qp_trie_get_leq(trie, key, len, dst);
}

int hattrie_del(hattrie_t *trie, const char* key, size_t len)
{
    return qp_trie_del(trie, key, len, NULL) ? 0 : -1;
}


hattrie_iter_t* hattrie_iter_begin(const hattrie_t *trie, bool sorted)
{
    UNUSED(sorted); // iteration over QP is always sorted ATM
    return qp_trie_it_begin(/*const-cast*/(hattrie_t*) trie);
}
void hattrie_iter_next(hattrie_iter_t *it)
{
    qp_trie_it_next(it); // TODO: ignored OOM
}
bool hattrie_iter_finished(hattrie_iter_t *it)
{
    return qp_trie_it_finished(it);
}
void hattrie_iter_free(hattrie_iter_t *it)
{
    qp_trie_it_free(it);
}
const char* hattrie_iter_key(hattrie_iter_t *it, size_t *plen)
{
    // it's a bit cumbersome to change the type of `plen` safely
    uint32_t len32;
    const char *res = qp_trie_it_key(it, &len32);
    if (plen)
        *plen = len32;
    return res;
}
value_t* hattrie_iter_val(hattrie_iter_t *it)
{
    return qp_trie_it_val(it);
}

