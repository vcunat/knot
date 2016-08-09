
#pragma once

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

#include "libknot/mm_ctx.h"

/*!
 * \file \brief Native API of QP-tries:
 *
 * - keys are char strings, not necessarily zero-terminated,
 *   the structure copies the contents of the passed keys
 * - values are typedef void* value_t, typically you get an ephemeral pointer to it
 * - key lengths are limited by 2^32-1 ATM
 */

/*! Opaque structure holding a QP-trie. */
struct qp_trie;
/*! Type of the values to be stored by the trie. */
typedef void* value_t;
/*! Opaque type for holding a QP-trie iterator. */
typedef struct qp_trie_it qp_trie_it_t;


/*! \brief Create a trie instance. */
struct qp_trie* Tcreate(knot_mm_t *mm);
/*! \brief Free a trie instance. */
void Tfree(struct qp_trie *tbl);
/*! \brief Clear a trie instance (make it empty). */
void Tclear(struct qp_trie *tbl);
/*! \brief Duplicate a trie instance, using a value_t transforming function.
 *
 *  If nval == NULL, make the new trie empty (but copy mm). */
struct qp_trie* Tdup(const struct qp_trie *tbl, value_t (*nval)(value_t));

/*! \brief Return the number of keys in the trie. */
size_t Tweight(const struct qp_trie *tbl);
/*! \brief Search the trie, returning NULL on failure. */
value_t* Tget_try(struct qp_trie *tbl, const char *key, uint32_t len);
/*! \brief Search the trie, inserting NULL value_t on failure. */
value_t* Tget_ins(struct qp_trie *tbl, const char *key, uint32_t len);

/*!
 * \brief Search for less-or-equal element.
 *
 * \param pval must be valid; it will be set to NULL if not found or errored.
 * Return 0 for exact match, -1 for previous, 1 for not-found, or KNOT_ENOMEM. */
int Tget_leq(struct qp_trie *tbl, const char *key, uint32_t len, value_t **pval);

/*! \brief Apply a function to every value_t*, in order. */
int Tapply(struct qp_trie *tbl, int (*f)(value_t*,void*), void* d);

/*! \brief TODO: this function isn't (yet ready to be) used. */
bool Tget_next(struct qp_trie *tbl, const char **pkey, uint32_t *plen, value_t **pval);

/*! \brief Remove an item, returning if succeeded.
 *
 * If val!=NULL and deletion succeeded, the deleted value is set. */
bool Tdel(struct qp_trie *tbl, const char *key, uint32_t len, value_t *pval);


/*! \brief Create a new iterator pointing to the first element (if any). */
qp_trie_it_t* Tit_begin(struct qp_trie *tbl);
/*!
 * \brief Advance the iterator to the next element.
 *
 * Iteration is in ascending lexicographical order.
 * In particular, the empty string would be considered as the very first. */
int Tit_next(qp_trie_it_t *it);
/*! \brief Test if the iterator has gone past the last element. */
bool Tit_finished(qp_trie_it_t *it);
/*! \brief Free any resources of the iterator. It's OK to call it on NULL. */
void Tit_free(qp_trie_it_t *it);
/*! \brief Return pointer to the key of the current element. */
const char* Tit_key(qp_trie_it_t *it, uint32_t *plen);
/*! \brief Return pointer to the value of the current element (writable). */
value_t* Tit_val(qp_trie_it_t *it);

