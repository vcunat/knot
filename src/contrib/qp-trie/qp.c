/*  Copyright (C) 2016 CZ.NIC, z.s.p.o. <knot-dns@labs.nic.cz>

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

    The code originated from https://github.com/fanf2/qp/blob/master/qp.c
    at revision 5f6d93753.
 */

#include <assert.h>
#include <stdlib.h>
#include <string.h>

#include "contrib/qp-trie/qp.h"
#include "contrib/mempattern.h"
#include "contrib/macros.h"
#include "libknot/errcode.h"


#if defined(__i386) || defined(__x86_64) || defined(_M_IX86) \
	|| (defined(__BYTE_ORDER__) && defined(__ORDER_LITTLE_ENDIAN) \
		&& __BYTE_ORDER__ == __ORDER_LITTLE_ENDIAN__)

	/*!
	 * \brief Use a pointer alignment hack to save memory.
	 *
	 * When on, isbranch() relies on the fact that in leaf_t the first pointer
	 * is aligned on multiple of 4 bytes and that the flags bitfield is
	 * overlaid over the lowest two bits of that pointer.
	 * Neither is really guaranteed by the C standards; the second part should
	 * be OK with x86_64 ABI and most likely any other little-endian platform.
	 * It would be possible to manipulate the right bits portably, but it would
	 * complicate the code nontrivially. C++ doesn't even guarantee type-punning.
	 * In debug mode we check this works OK when creating a new trie instance.
	 */
	#define FLAGS_HACK 1
#else
	#define FLAGS_HACK 0
#endif


typedef unsigned char byte;
typedef unsigned int uint;
typedef uint bitmap_t; /*! Bit-maps, using the range of 1<<0 to 1<<16 (inclusive). */


/*! \brief A trie node is either leaf_t or branch_t. */
typedef union node node_t;

/*! \brief What we use as trie key internally. */
typedef struct tkey tkey_t;
/*! \brief Leaf of trie. */
typedef struct leaf {
	#if !FLAGS_HACK
		byte flags;
	#endif
	tkey_t *key; /*!< The pointer must be aligned to 4-byte multiples! */
	value_t val;
} leaf_t;
struct tkey {
	uint32_t len; // 32 bits are enough for key lengths; probably even 16 bits would be.
	char chars[];
};

/*!
 * \brief Branch node of trie.
 *
 * - The flags distinguish whether the node is a leaf_t (0), or a branch
 *   testing the more-important nibble (1) or the less-important one (2).
 * - It stores the index of the byte that the node tests.  The combined
 *   value (index*4 + flags) increases in branch nodes as you go deeper
 *   into the trie.  All the keys below a branch are identical up to the
 *   nibble identified by the branch.  Indices have to be stored because
 *   we skip any branch nodes that would have a single child.
 *   (Consequently, the skipped parts of key have to be validated in a leaf.)
 * - The bitmap indicates which subtries are present.  The present child nodes
 *   are stored in the twigs array (with no holes between them).
 * - To simplify storing keys that are prefixes of each other, the end-of-string
 *   position is treated as another nibble value, ordered before all others.
 *   That affects the bitmap and twigs fields.
 * \note The branch nodes are never allocated individually, but they are
 *   always part of either the root node or the twigs array of the parent.
 */
typedef struct branch {
	#if FLAGS_HACK
		uint32_t flags : 2,
			bitmap : 17; /*!< The first bitmap bit is for end-of-string child. */
	#else
		byte flags;
		uint32_t bitmap;
	#endif
	uint32_t index;
	node_t *twigs;
} branch_t;

union node {
	struct leaf leaf;
	struct branch branch;
};

typedef struct qp_trie {
	node_t root; // undefined when weight == 0, see empty_root()
	size_t weight;
	knot_mm_t mm;
} trie_t;

/*! \brief Make the root node empty (debug-only). */
static inline void empty_root(node_t *root) {
#ifndef NDEBUG
	*root = (node_t){ .branch = {
		.flags = 3, // invalid value that fits
		.bitmap = 0,
		.index = -1,
		.twigs = NULL
	} };
#endif
}

/*! \brief Check that unportable code works OK (debug-only). */
static void assert_portability(void) {
#if FLAGS_HACK
	assert(
		((union node){ .leaf = { .key = ((void *)NULL)+1, .val = NULL } }
			).branch.flags == 1
	);
#endif
}

/*! \brief Propagate error codes. */
#define ERR_RETURN(x) \
	do { \
		int err_code_ = x; \
		if (unlikely(err_code_)) \
			return err_code_; \
	} while (false)

/*!
 * \brief Count the number of set bits.
 *
 * \TODO This implementation may be relatively slow on some HW.
 */
static uint bitmap_weight(bitmap_t w)
{
	assert((w & ~((1<<17)-1)) == 0); // using the least-important 17 bits
	return __builtin_popcount(w);
}

/*! \brief Test flags to determine type of this node. */
static bool isbranch(const node_t *t)
{
	uint f = t->branch.flags;
	assert(f <= 2);
	return f != 0;
}

/*! \brief Make a bitmask for testing a branch bitmap. */
static bitmap_t nibbit(byte k, uint flags)
{
	uint shift = (2 - flags) << 2;
	uint nibble = (k >> shift) & 0xf;
	return 1 << (nibble + 1/*because of prefix keys*/);
}

/*! \brief Extract a nibble from a key and turn it into a bitmask. */
static bitmap_t twigbit(node_t *t, const char *key, uint32_t len)
{
	assert(isbranch(t));
	uint i = t->branch.index;

	if (i >= len)
		return 1 << 0; // leaf position

	return nibbit((byte)key[i], t->branch.flags);
}

/*! \brief Test if a branch node has a child indicated by a bitmask. */
static bool hastwig(node_t *t, bitmap_t bit)
{
	assert(isbranch(t));
	return t->branch.bitmap & bit;
}

/*! \brief Compute offset of an existing child in a branch node. */
static uint twigoff(node_t *t, bitmap_t b)
{
	assert(isbranch(t));
	return bitmap_weight(t->branch.bitmap & (b-1));
}

/*! \brief Get pointer to a particular child of a branch node. */
static node_t* twig(node_t *t, uint i)
{
	assert(isbranch(t));
	return &t->branch.twigs[i];
}

/*!
 * \brief For a branch nod, compute offset of a child and child count.
 *
 * Having this separate might be meaningful for performance optimization.
 */
#define TWIGOFFMAX(off, max, t, b) do {			\
		off = twigoff(t, b);			\
		max = bitmap_weight(t->branch.bitmap);	\
	} while(0)

/*! \brief Simple string comparator, taken from hhash.c */
static int key_cmp(const char *k1, uint32_t k1_len, const char *k2, uint32_t k2_len)
{
	int ret = memcmp(k1, k2, MIN(k1_len, k2_len));
	if (ret != 0) {
		return ret;
	}

	/* Key string is equal, compare lengths. */
	if (k1_len == k2_len) {
		return 0;
	} else if (k1_len < k2_len) {
		return -1;
	}

	return 1;
}

struct qp_trie* qp_trie_create(knot_mm_t *mm)
{
	assert_portability();
	trie_t *trie = mm_alloc(mm, sizeof(trie_t));
	if (trie != NULL) {
		empty_root(&trie->root);
		trie->weight = 0;
		if (mm != NULL)
			trie->mm = *mm;
		else
			mm_ctx_init(&trie->mm);
	}
	return trie;
}

/*! \brief Free anything under the trie node, except for the passed pointer itself. */
static void clear_trie(node_t *trie, knot_mm_t *mm)
{
	if (!isbranch(trie)) {
		mm_free(mm, trie->leaf.key);
	} else {
		branch_t *b = &trie->branch;
		int len = bitmap_weight(b->bitmap);
		for (int i = 0; i < len; ++i)
			clear_trie(b->twigs + i, mm);
		mm_free(mm, b->twigs);
	}
}
void qp_trie_free(struct qp_trie *tbl)
{
	if (tbl == NULL)
		return;
	if (tbl->weight)
		clear_trie(&tbl->root, &tbl->mm);
	mm_free(&tbl->mm, tbl);
}

void qp_trie_clear(struct qp_trie *tbl)
{
	assert(tbl);
	if (!tbl->weight)
		return;
	clear_trie(&tbl->root, &tbl->mm);
	empty_root(&tbl->root);
	tbl->weight = 0;
}

/*! \brief Duplicate everything under the trie node (assumed allocated itself). */
static int dup_trie(const node_t *t1, node_t *t2, value_t (*nval)(value_t), knot_mm_t *mm)
{
	if (!isbranch(t1)) {
		tkey_t *key1 = t1->leaf.key;
		tkey_t *key2 = mm_alloc(mm, sizeof(tkey_t) + key1->len);
		if (!key2)
			return KNOT_ENOMEM;
		key2->len = key1->len;
		memcpy(key2->chars, key1->chars, key1->len);
		t2->leaf.key = key2;
		t2->leaf.val = nval(t1->leaf.val);
		return 0;
	}
	memcpy(t2, t1, sizeof(branch_t)); // flags etc.; will rewrite the pointer
	int child_count = bitmap_weight(t1->branch.bitmap);
	t2->branch.twigs = mm_alloc(mm, sizeof(node_t) * child_count);
	node_t *twigs1 = t1->branch.twigs;
	node_t *twigs2 = t2->branch.twigs;
	if (unlikely(!twigs2))
		return KNOT_ENOMEM;
	for (int i = 0; i < child_count; ++i) {
		int err = dup_trie(twigs1 + i, twigs2 + i, nval, mm);
		if (unlikely(err)) { // error: we need to free already allocated stuff
			while (--i >= 0)
				clear_trie(twigs2 + i, mm);
			return err;
		};
	}
	return 0;
}
trie_t* qp_trie_dup(const struct qp_trie *tbl, value_t (*nval)(value_t))
{
	trie_t *t = mm_alloc(/*const-cast*/(knot_mm_t*)&tbl->mm, sizeof(trie_t));
	if (unlikely(!t))
		return NULL;
	t->mm = tbl->mm;
	if (!nval) {
		t->weight = 0;
		return t;
	}
	t->weight = tbl->weight;
	if (unlikely(!dup_trie(&tbl->root, &t->root, nval, &t->mm))) {
		qp_trie_free(t);
		return NULL;
	};
	return t;
}


size_t qp_trie_weight(const struct qp_trie *tbl)
{
	return tbl ? tbl->weight : 0; // for some reason, HAT supports this on NULL
}

value_t* qp_trie_get_try(trie_t *tbl, const char *key, uint32_t len)
{
	assert(tbl);
	if (!tbl->weight)
		return NULL;
	node_t *t = &tbl->root;
	while (isbranch(t)) {
		__builtin_prefetch(t->branch.twigs);
		bitmap_t b = twigbit(t, key, len);
		if (!hastwig(t, b))
			return NULL;
		t = twig(t, twigoff(t, b));
	}
	if (key_cmp(key, len, t->leaf.key->chars, t->leaf.key->len) != 0)
		return NULL;
	return &t->leaf.val;
}

int qp_trie_del(struct qp_trie *tbl, const char *key, uint32_t len, value_t *pval)
{
	assert(tbl);
	if (!tbl->weight)
		return 1;
	node_t *t = &tbl->root; // current and parent node
	branch_t *p = NULL;
	bitmap_t b = 0;
	while (isbranch(t)) {
		__builtin_prefetch(t->branch.twigs);
		b = twigbit(t, key, len);
		if (!hastwig(t, b))
			return 1;
		p = &t->branch;
		t = twig(t, twigoff(t, b));
	}
	if (key_cmp(key, len, t->leaf.key->chars, t->leaf.key->len) != 0)
		return 1;
	mm_free(&tbl->mm, t->leaf.key);
	if (pval != NULL)
		*pval = t->leaf.val; // we return value_t directly when deleting
	--tbl->weight;
	if (unlikely(!p)) { // whole trie was a single leaf
		assert(tbl->weight == 0);
		empty_root(&tbl->root);
		return 0;
	}
	// remove leaf t as child of p
	int ci = t - p->twigs, // child index via pointer arithmetic
	    cc = bitmap_weight(p->bitmap); // child count
	assert(ci >= 0 && ci < cc);

	if (cc == 2) { // collapse binary node p: move the other child to this node
		node_t *twigs = p->twigs;
		(*(node_t*)p) = twigs[1-ci]; // it might be a leaf or branch
		mm_free(&tbl->mm, twigs);
		return 0;
	}
	memmove(p->twigs+ci, p->twigs+ci+1, sizeof(node_t) * (cc - ci - 1));
	p->bitmap &= ~b;
	node_t *twigs = mm_realloc(&tbl->mm,
			p->twigs, sizeof(node_t) * (cc - 1), sizeof(node_t) * cc);
	if (likely(twigs != NULL))
		p->twigs = twigs;
		/* We can ignore mm_realloc failure, only beware that next time
		 * the prev_size passed to it wouldn't be correct; TODO? */
	return 0;
}

/*!
 * \brief Stack of nodes, storing a path down a trie.
 *
 * The structure also serves directly as the public qp_trie_it_t type,
 * in which case it always points to the current leaf, unless we've finished
 * (i.e. it->len == 0).
 */
typedef struct qp_trie_it {
	node_t* *stack;  /*!< The stack; malloc is used directly instead of mm. */
	uint32_t len;  /*!< Current length of the stack. */
	uint32_t alen; /*!< Allocated/available length of the stack. */
	/*! \brief Initial storage for \a stack; it should fit in most use cases. */
	node_t* stack_init[2000 / sizeof(node_t*)];
} nstack_t;

/*! \brief Create a node stack containing just the root (or empty). */
static void ns_init(nstack_t *ns, struct qp_trie *tbl)
{
	assert(tbl);
	ns->stack = ns->stack_init;
	ns->alen = sizeof(ns->stack_init) / sizeof(ns->stack_init[0]);
	if (tbl->weight) {
		ns->len = 1;
		ns->stack[0] = &tbl->root;
	} else {
		ns->len = 0;
	}
}

/*! \brief Free inside of the stack, i.e. not the passed pointer itself. */
static void ns_cleanup(nstack_t *ns)
{
	assert(ns && ns->stack);
	if (likely(ns->stack == ns->stack_init))
		return;
	free(ns->stack);
	#ifndef NDEBUG
		ns->stack = NULL;
		ns->alen = 0;
	#endif
}

/*! \brief Allocate more space for the stack. */
static int ns_longer_alloc(nstack_t *ns)
{
	ns->alen *= 2;
	size_t new_size = sizeof(nstack_t) + ns->alen * sizeof(node_t*);
	node_t* *st;
	if (ns->stack == ns->stack_init) {
		st = malloc(new_size);
		if (st != NULL)
			memcpy(st, ns->stack, ns->len * sizeof(node_t*));
	} else {
		st = realloc(ns->stack, new_size);
	}
	if (st == NULL)
		return KNOT_ENOMEM;
	ns->stack = st;
	return 0;
}
/*! \brief Ensure the node stack can be extended by one. */
static inline int ns_longer(nstack_t *ns)
{
	// get a longer stack if needed
	if (likely(ns->len < ns->alen))
		return 0;
	return ns_longer_alloc(ns); // hand-split the part suitable for inlining
}

/*!
 * \brief Find the "branching point" as if searching for a key.
 *
 *  The whole path to the point is kept on the passed stack;
 *  always at least the root will remain on the top of it.
 *  Beware: the precise semantics of this function is rather tricky.
 *  The top of the stack will contain: the corresponding leaf if exact match is found;
 *  or the immediate node below a branching-point-on-edge or the branching-point itself.
 *  \param pinfo Set position of the point of first mismatch (in index and flags).
 *  \param pfirst Set the value of the first non-matching character (from trie),
 *      optionally; end-of-string character has value -256 (that's why it's int).
 *  Return 0 or KNOT_ENOMEM.
 */
static int ns_find_branch(nstack_t *ns, const char *key, uint32_t len
		, branch_t *pinfo, int *pfirst)
{
	assert(ns && ns->len && pinfo);
	// First find some leaf with longest matching prefix.
	while (isbranch(ns->stack[ns->len - 1])) {
		ERR_RETURN(ns_longer(ns));
		node_t *t = ns->stack[ns->len - 1];
		__builtin_prefetch(t->branch.twigs);
		bitmap_t b = twigbit(t, key, len);
		// Even if our key is missing from this branch we need to
		// keep iterating down to a leaf. It doesn't matter which
		// twig we choose since the keys are all the same up to this
		// index. Note that blindly using twigoff(t, b) can cause
		// an out-of-bounds index if it equals twigmax(t).
		uint i = hastwig(t, b) ? twigoff(t, b) : 0;
		ns->stack[ns->len++] = twig(t, i);
	}
	tkey_t *lkey = ns->stack[ns->len-1]->leaf.key;
	// Find index of the first char that differs.
	uint32_t index = 0;
	while (index < MIN(len,lkey->len)) {
		if (key[index] != lkey->chars[index])
			break;
		else
			++index;
	}
	pinfo->index = index;
	if (pfirst)
		*pfirst = lkey->len > index ? lkey->chars[index] : -256;
	// Find flags: which half-byte has matched.
	uint flags;
	if (index == len && len == lkey->len) { // found equivalent key
		pinfo->flags = flags = 0;
		goto success;
	}
	if (likely(index < MIN(len,lkey->len))) {
		byte k2 = (byte)lkey->chars[index];
		byte k1 = (byte)key[index];
		flags = ((k1 ^ k2) & 0xf0) ? 1 : 2;
	} else { // one is prefix of another
		flags = 1;
	}
	pinfo->flags = flags;
	// now go up the trie from the current leaf
	branch_t *t;
	do {
		if (unlikely(ns->len == 1))
			goto success; // only the root stays on the stack
		t = (branch_t*)ns->stack[ns->len-2];
		if (t->index < index || (t->index == index && t->flags < flags))
			goto success;
		--ns->len;
	} while (true);
success:
	#ifndef NDEBUG // invariants on successful return
		assert(ns->len);
		if (isbranch(ns->stack[ns->len-1])) {
			t = &ns->stack[ns->len-1]->branch;
			assert(t->index > index || (t->index == index && t->flags >= flags));
		}
		if (ns->len > 1) {
			t = &ns->stack[ns->len-2]->branch;
			assert(t->index < index || (t->index == index
						&& (t->flags < flags || (t->flags == 1 && flags == 0))));
		}
	#endif
	return 0;
}

/*!
 * \brief Advance the node stack to the last leaf in the subtree.
 *
 * \return 0 or KNOT_ENOMEM.
 */
static int ns_last_leaf(nstack_t *ns)
{
	assert(ns);
	do {
		ERR_RETURN(ns_longer(ns));
		node_t *t = ns->stack[ns->len - 1];
		if (!isbranch(t))
			return 0;
		int lasti = bitmap_weight(t->branch.bitmap) - 1;
		assert(lasti >= 0);
		ns->stack[ns->len++] = twig(t, lasti);
	} while (true);
}
/*!
 * \brief Advance the node stack to the first leaf in the subtree.
 *
 * \return 0 or KNOT_ENOMEM.
 */
static int ns_first_leaf(nstack_t *ns)
{
	assert(ns && ns->len);
	do {
		ERR_RETURN(ns_longer(ns));
		node_t *t = ns->stack[ns->len - 1];
		if (!isbranch(t))
			return 0;
		ns->stack[ns->len++] = twig(t, 0);
	} while (true);
}

/*!
 * \brief Advance the node stack to the leaf that is previous to the current node.
 *
 * \note Prefix leaf under the current node DOES count (if present; perhaps questionable).
 * \return 0 on success, 1 on not-found, or possibly KNOT_ENOMEM.
 */
static int ns_prev_leaf(nstack_t *ns)
{
	assert(ns && ns->len > 0);

	node_t *t = ns->stack[ns->len-1];
	if (hastwig(t, 1<<0)) { // the prefix leaf
		t = twig(t, 0);
		ERR_RETURN(ns_longer(ns));
		ns->stack[ns->len++] = t;
		return 0;
	}

	do {
		if (ns->len < 2)
			return 1; // root without empty key has no previous leaf
		t = ns->stack[ns->len-1];
		node_t *p = ns->stack[ns->len-2];
		int pindex = t - p->branch.twigs; // index in parent via pointer arithmetic
		assert(pindex >= 0 && pindex <= 16);
		if (pindex > 0) { // t isn't the first child -> go down the previous one
			ns->stack[ns->len-1] = twig(p, pindex-1);
			return ns_last_leaf(ns);
		}
		// we've got to go up again
		--ns->len;
	} while (true);
}
/*!
 * \brief Advance the node stack to the leaf that is successor to the current node.
 *
 * \note Prefix leaf or anything else under the current node DOES count.
 * Return 0 on success, 1 on not-found, or possibly KNOT_ENOMEM.
 */
static int ns_next_leaf(nstack_t *ns)
{
	assert(ns && ns->len > 0);

	node_t *t = ns->stack[ns->len-1];
	if (isbranch(t))
		return ns_first_leaf(ns);

	do {
		if (ns->len < 2)
			return 1; // not found, as no more parent is available
		t = ns->stack[ns->len-1];
		node_t *p = ns->stack[ns->len-2];
		int pindex = t - p->branch.twigs; // index in parent via pointer arithmetic
		assert(pindex >= 0 && pindex <= 16);
		int pcount = bitmap_weight(p->branch.bitmap);
		if (pindex+1 < pcount) { // t isn't the last child -> go down the next one
			ns->stack[ns->len-1] = twig(p, pindex+1);
			return ns_first_leaf(ns);
		}
		// we've got to go up again
		--ns->len;
	} while (true);
}

int qp_trie_get_leq(struct qp_trie *tbl, const char *key, uint32_t len, value_t **pval)
{
	assert(tbl && pval);
	*pval = NULL; // so on failure we can just return 1;
	if (tbl->weight == 0)
		return 1;
	// First find a key with longest-matching prefix
	__attribute__((cleanup(ns_cleanup)))
		nstack_t ns_local;
	nstack_t *ns = &ns_local;
	ns_init(ns, tbl);
	branch_t bp;
	int un_leaf; // first unmatched character in the leaf
	ERR_RETURN(ns_find_branch(ns, key, len, &bp, &un_leaf));
	int un_key = bp.index < len ? key[bp.index] : -256;
	node_t *t = ns->stack[ns->len-1];
	if (bp.flags == 0) { // found exact match
		if (pval)
			*pval = &t->leaf.val;
		return 0;
	}
	// Get t: the last node on matching path
	if (isbranch(t) && t->branch.index == bp.index && t->branch.flags == bp.flags) {
		// t is OK
	} else {
		// the top of the stack was the first unmatched node -> step up
		if (ns->len == 1) {
			// root was unmatched already
			if (un_key < un_leaf)
				return 1;
			ERR_RETURN(ns_last_leaf(ns));
			goto success;
		}
		--ns->len;
		t = ns->stack[ns->len-1];
	}
	// Now we re-do the first "non-matching" step in the trie
	// but try the previous child if key was less (it may not exist)
	bitmap_t b = twigbit(t, key, len);
	int i = hastwig(t, b)
		? twigoff(t, b) - (un_key < un_leaf)
		: twigoff(t, b) - 1 /*twigoff returns successor when !hastwig*/;
	if (i >= 0) {
		ERR_RETURN(ns_longer(ns));
		ns->stack[ns->len++] = twig(t, i);
		ERR_RETURN(ns_last_leaf(ns));
	} else {
		ERR_RETURN(ns_prev_leaf(ns)); // KNOT_ENOMEM or 1 for no-leq
	}
success:
	assert(!isbranch(ns->stack[ns->len-1]));
	*pval = & ns->stack[ns->len-1]->leaf.val;
	return -1;
}

/*! \brief Initialize a new leaf, copying the key, and returning failure code. */
static int mk_leaf(node_t *leaf, const char *key, uint32_t len, knot_mm_t *mm)
{
	tkey_t *k = mm_alloc(mm, sizeof(tkey_t) + len);
	#if FLAGS_HACK
		assert(((uintptr_t)k) % 4 == 0); // we need an aligned pointer
	#endif
	if (unlikely(!k))
		return KNOT_ENOMEM;
	k->len = len;
	memcpy(k->chars, key, len);
	leaf->leaf = (leaf_t){
		#if !FLAGS_HACK
			.flags = 0,
		#endif
		.val = NULL,
		.key = k
	};
	return 0;
}

value_t* qp_trie_get_ins(struct qp_trie *tbl, const char *key, uint32_t len)
{
	assert(tbl);
	// First leaf in an empty tbl?
	if (unlikely(!tbl->weight)) {
		if (unlikely(mk_leaf(&tbl->root, key, len, &tbl->mm)))
			return NULL;
		++tbl->weight;
		return &tbl->root.leaf.val;
	}
	// Find the branching-point
	__attribute__((cleanup(ns_cleanup)))
		nstack_t ns_local;
	nstack_t *ns = &ns_local;
	ns_init(ns, tbl);
	branch_t bp; // branch-point: index and flags signifying the longest common prefix
	int k2; // the first unmatched character in the leaf
	if (unlikely(ns_find_branch(ns, key, len, &bp, &k2)))
		return NULL;
	node_t *t = ns->stack[ns->len - 1];
	if (bp.flags == 0) // the same key was already present
		return &t->leaf.val;
	node_t leaf;
	if (unlikely(mk_leaf(&leaf, key, len, &tbl->mm)))
		return NULL;

	if (isbranch(t) && bp.index == t->branch.index && bp.flags == t->branch.flags) {
		// The node t needs a new leaf child.
		bitmap_t b1 = twigbit(t, key, len);
		assert(!hastwig(t, b1));
		uint s, m; TWIGOFFMAX(s, m, t, b1); // new child position and original child count
		node_t *twigs = mm_realloc(&tbl->mm, t->branch.twigs,
				sizeof(node_t) * (m + 1), sizeof(node_t) * m);
		if (unlikely(!twigs))
			goto err_leaf;
		memmove(twigs+s+1, twigs+s, sizeof(node_t) * (m - s));
		twigs[s] = leaf;
		t->branch.twigs = twigs;
		t->branch.bitmap |= b1;
		++tbl->weight;
		return &twigs[s].leaf.val;
	} else {
		// We need to insert a new binary branch with leaf at *t.
		// Note: it works the same for the case where we insert above root t.
		#ifndef NDEBUG
			if (ns->len > 1) {
				node_t *pt = ns->stack[ns->len-2];
				assert(hastwig(pt, twigbit(pt, key, len)));
			}
		#endif
		node_t *twigs = mm_alloc(&tbl->mm, sizeof(node_t) * 2);
		if (unlikely(!twigs))
			goto err_leaf;
		node_t t2 = *t; // Save before overwriting t.
		t->branch = bp; // copy flags and index
		t->branch.twigs = twigs;
		bitmap_t b1 = twigbit(t, key, len);
		bitmap_t b2 = unlikely(k2 == -256) ? (1<<0) : nibbit(k2, bp.flags);
		t->branch.bitmap = b1 | b2;
		*twig(t, twigoff(t, b1)) = leaf;
		*twig(t, twigoff(t, b2)) = t2;
		++tbl->weight;
		return &twig(t, twigoff(t, b1))->leaf.val;
	};
err_leaf:
	mm_free(&tbl->mm, leaf.leaf.key);
	return NULL;
}

/*! \brief Apply a function to every value_t*, in order; a recursive solution. */
static int apply_trie(node_t *t, int (*f)(value_t*,void*), void* d)
{
	assert(t);
	if (!isbranch(t))
		return f(&t->leaf.val, d);
	int child_count = bitmap_weight(t->branch.bitmap);
	for (int i = 0; i < child_count; ++i)
		ERR_RETURN(apply_trie(twig(t, i), f, d));
	return 0;
}
int qp_trie_apply(struct qp_trie *tbl, int (*f)(value_t*,void*), void* d)
{
	assert(tbl && f);
	if (!tbl->weight)
		return 0;
	return apply_trie(&tbl->root, f, d);
}

/* These are all thin wrappers around static Tns* functions. */
qp_trie_it_t* qp_trie_it_begin(struct qp_trie *tbl)
{
	assert(tbl);
	qp_trie_it_t *it = malloc(sizeof(nstack_t));
	if (!it)
		return NULL;
	ns_init(it, tbl);
	if (it->len == 0) // empty tbl
		return it;
	if (ns_first_leaf(it)) {
		ns_cleanup(it);
		free(it);
		return NULL;
	}
	return it;
}
int qp_trie_it_next(qp_trie_it_t *it)
{
	assert(it && it->len);
	int err = ns_next_leaf(it);
	if (err == 1)
		it->len = 0; // just finished
	return err;
}
bool qp_trie_it_finished(qp_trie_it_t *it)
{
	assert(it);
	return it->len == 0;
}
void qp_trie_it_free(qp_trie_it_t *it)
{
	if (!it)
		return;
	ns_cleanup(it);
	free(it);
}
const char* qp_trie_it_key(qp_trie_it_t *it, uint32_t *len)
{
	assert(it && it->len);
	node_t *t = it->stack[it->len-1];
	assert(!isbranch(t));
	tkey_t *key = t->leaf.key;
	if (len)
		*len = key->len;
	return key->chars;
}
value_t* qp_trie_it_val(qp_trie_it_t *it)
{
	assert(it && it->len);
	node_t *t = it->stack[it->len-1];
	assert(!isbranch(t));
	return &t->leaf.val;
}

