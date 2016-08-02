
#pragma once

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

#include "libknot/mm_ctx.h"

typedef void* value_t;
// Native API of QP-tries
struct Tbl;
/*! \brief Create a trie instance. */
struct Tbl* Tcreate(knot_mm_t *mm);
/*! \brief Free a trie instance. */
void Tfree(struct Tbl *tbl);

/*! \brief Return the number of keys in the trie. */
size_t Tweight(const struct Tbl *tbl);
/*! \brief Search the trie, returning NULL on failure. */
value_t* Tget_try(struct Tbl *tbl, const char *key, size_t len);
/*! \brief Search the trie, inserting NULL value_t on failure. */
value_t* Tget_ins(struct Tbl *tbl, const char *key, size_t len);


bool Tget_next(struct Tbl *tbl, const char **pkey, size_t *plen, value_t **pval);

struct Tbl* Tdelkv(struct Tbl *tbl, const char *key, size_t len, const char **pkey, void **pval);

