
#pragma once

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

#include "libknot/mm_ctx.h"

/** Native API of QP-tries:
 *	- keys are char strings, not necessarily zero-terminated,
 *	  the structure can only copy the contents
 *	- values are typedef void* value_t, typically you get an ephemeral pointer to it
 *	- admissible key lengths are up to 2^32-1 ATM
 */

typedef void* value_t;
typedef struct TnodeStack Tit_t;


struct Tbl;
/*! \brief Create a trie instance. */
struct Tbl* Tcreate(knot_mm_t *mm);
/*! \brief Free a trie instance. */
void Tfree(struct Tbl *tbl);
/*! \brief Clear a trie instance (make it empty). */
void Tclear(struct Tbl *tbl);
/*! \brief Duplicate a trie instance, using a value_t transforming function.
 *
 *  If nval == NULL, make the new trie empty (but copy mm). */
struct Tbl* Tdup(const struct Tbl *tbl, value_t (*nval)(value_t));

/*! \brief Return the number of keys in the trie. */
size_t Tweight(const struct Tbl *tbl);
/*! \brief Search the trie, returning NULL on failure. */
value_t* Tget_try(struct Tbl *tbl, const char *key, uint32_t len);
/*! \brief Search the trie, inserting NULL value_t on failure. */
value_t* Tget_ins(struct Tbl *tbl, const char *key, uint32_t len);

/*! \brief Search for less-or-equal element.
 *
 * \param pval must be valid; it will be set to NULL if not found or errored.
 * Return 0 for exact match, -1 for previous, 1 for not-found, or KNOT_ENOMEM. */
int Tget_leq(struct Tbl *tbl, const char *key, uint32_t len, value_t **pval);

/*! \brief Apply a function to every value_t*, in order. */
int Tapply(struct Tbl *tbl, int (*f)(value_t*,void*), void* d);


bool Tget_next(struct Tbl *tbl, const char **pkey, uint32_t *plen, value_t **pval);

/*! \brief Remove an item, returning if succeeded.
 *
 * If val!=NULL and deletion succeeded, the deleted value is set. */
bool Tdel(struct Tbl *tbl, const char *key, uint32_t len, value_t *pval);


/*! Creates a new iterator pointing to the first element (if any). */
Tit_t* Tit_begin(struct Tbl *tbl);

int Tit_next(Tit_t *it);

bool Tit_finished(Tit_t *it);

void Tit_free(Tit_t *it);

const char* Tit_key(Tit_t *it, uint32_t *plen);

value_t* Tit_val(Tit_t *it);

