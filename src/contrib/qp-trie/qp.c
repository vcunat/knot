// qp.c: tables implemented with quadbit popcount patricia tries.
//
// Written by Tony Finch <dot@dotat.at>
// You may do anything with this. It has no warranty.
// <http://creativecommons.org/publicdomain/zero/1.0/>

// TODO: cleanup headers
#include <assert.h>
#include <errno.h>
#include <stdlib.h>
#include <string.h>

#include "contrib/qp-trie/qp.h"
#include "contrib/mempattern.h"
#include "contrib/macros.h"
#include "libknot/errcode.h"





typedef unsigned char byte;
typedef unsigned int uint;

typedef uint Tbitmap;

/*! \brief Propagate error codes. */
#define ERR_RETURN(x) \
	do { \
		int err_code_ = x; \
		if (unlikely(err_code_)) \
			return err_code_; \
	} while (false)


static uint popcount(Tbitmap w) {
	uint result = __builtin_popcount(w);
	assert(result <= 17);
	return result;
	// TODO: this implementation may be relatively slow on some HW
}

/*
// Parallel popcount of the top and bottom 16 bits in a 32 bit word. This
// is probably only a win if your CPU is short of registers and/or integer
// units. NOTE: The caller needs to extract the results by masking with
// 0x00FF0000 and 0x000000FF for the top and bottom halves.
static uint popcount16x2(uint w) {
	w -= (w >> 1) & 0x55555555;
	w = (w & 0x33333333) + ((w >> 2) & 0x33333333);
	w = (w + (w >> 4)) & 0x0F0F0F0F;
	w = w + (w >> 8);
	return(w);
}
*/

// A trie node is two words on 64 bit machines, or three on 32 bit
// machines. A node can be a leaf or a branch. In a leaf, the value
// pointer must be word-aligned to allow for the tag bits.

/*! \brief What we use as trie key internally. */
typedef struct Tkey {
	uint32_t len; // 32 bits are enough for key lengths; probably even 16 bits would be.
	char chars[];
} Tkey;

typedef struct Tleaf {
	Tkey *key;
	value_t val;
} Tleaf;

// Branch nodes are distinguished from leaf nodes using a couple
// of flag bits which act as a dynamic type tag. They can be:
//
// 0 -> node is a leaf
// 1 -> node is a branch, testing more-important nibble
// 2 -> node is a branch, testing less-important nibble
//
// A branch node is laid out so that the flag bits correspond to the
// least significant bits of one of the leaf node pointers. In a
// leaf node, that pointer must be word-aligned so that its flag bits
// are zero. We have chosen to place this restriction on the value
// pointer.
//
// A branch contains the index of the byte that it tests. The combined
// value index << 2 | flags increases along the key in big-endian
// lexicographic order, and increases as you go deeper into the trie.
// All the keys below a branch are identical up to the nibble
// identified by the branch.
//
// A branch has a bitmap of which subtries ("twigs") are present. The
// flags, index, and bitmap are packed into one word. The other word
// is a pointer to an array of trie nodes, one for each twig that is
// present.

// XXX We hope that the compiler will not punish us for abusing unions.

// XXX This currently assumes a 64 bit little endian machine.
// On a 32 bit machine we could perhaps fit a branch in to two words
// without restricting the key length by making the index relative
// instead of absolute. If the gap between nodes is larger than a 16
// bit offset allows, we can insert a stepping-stone branch with only
// one twig. This would make the code a bit more complicated...

typedef struct Tbranch {
	uint64_t
		flags : 2,
		index : 45,
		bitmap : 17; // the first bit is for end-of-string child
	union Trie *twigs;
	/* TODO: other than x86_64 ABI might be broken.
	 * > The order of bit fields within an allocation unit is undefined by standard!
	 * http://en.cppreference.com/w/c/language/bit_field
	 * but it's in ABI
	 * https://gcc.gnu.org/onlinedocs/gcc-6.1.0/gcc/Structures-unions-enumerations-and-bit-fields-implementation.html#Structures-unions-enumerations-and-bit-fields-implementation
	 * http://www.x86-64.org/documentation/abi.pdf (pg. 13,14)
	 * */
} Tbranch;

typedef union Trie {
	struct Tleaf leaf;
	struct Tbranch branch;
} Trie;

typedef struct Tbl {
	union Trie root; // undefined when weight == 0, preferably all zeroed
	size_t weight;
	knot_mm_t mm;
} Tbl;

/*! \brief Test flags to determine type of this node. */
static bool isbranch(const Trie *t) {
	return t->branch.flags != 0;
}

/*! \brief Make a bitmask for testing a branch bitmap. */
static Tbitmap nibbit(byte k, uint flags) {
	uint shift = (2 - flags) << 2;
	uint nibble = (k >> shift) & 0xf;
	return 1 << (nibble + 1/*because of prefix keys*/);
}

/*~ \brief Extract a nibble from a key and turn it into a bitmask. */
static Tbitmap twigbit(Trie *t, const char *key, uint32_t len) {
	assert(isbranch(t));
	uint i = t->branch.index;

	if (i >= len)
		return 1 << 0; // leaf position

	return nibbit((byte)key[i], t->branch.flags);
}

static bool hastwig(Trie *t, Tbitmap bit) {
	assert(isbranch(t));
	return t->branch.bitmap & bit;
}

static uint twigoff(Trie *t, Tbitmap b) {
	assert(isbranch(t));
	return popcount(t->branch.bitmap & (b-1));
}

static Trie* twig(Trie *t, uint i) {
	assert(isbranch(t));
	return &t->branch.twigs[i];
}

#define TWIGOFFMAX(off, max, t, b) do {			\
		off = twigoff(t, b);			\
		max = popcount(t->branch.bitmap);	\
	} while(0)

/*! \brief Item comparator from hhash.c */
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

struct Tbl* Tcreate(knot_mm_t *mm) {
	Tbl *trie = mm_alloc(mm, sizeof(Tbl));
	if (trie != NULL)
		trie->root = (Trie) { .leaf = { NULL, NULL } };
		trie->weight = 0;
		if (mm != NULL)
			trie->mm = *mm;
		else
			mm_ctx_init(&trie->mm);
	return trie;
}

/* Free anything under the trie node, except for the passed pointer itself. */
static void TfreeTrie(union Trie *trie, knot_mm_t *mm) {
	if (!isbranch(trie)) {
		mm_free(mm, trie->leaf.key);
	} else {
		Tbranch *b = &trie->branch;
		int len = popcount(b->bitmap);
		for (int i = 0; i < len; ++i)
			TfreeTrie(b->twigs + i, mm);
		mm_free(mm, b->twigs);
	}
}
void Tfree(struct Tbl *tbl) {
	if (tbl == NULL)
		return;
	if (tbl->weight)
		TfreeTrie(&tbl->root, &tbl->mm);
	mm_free(&tbl->mm, tbl);
}

void Tclear(struct Tbl *tbl) {
	assert(tbl);
	if (!tbl->weight)
		return;
	TfreeTrie(&tbl->root, &tbl->mm);
	tbl->root = (Trie) { .leaf = { NULL, NULL } };
	tbl->weight = 0;
}

/*! \brief Duplicate everything under the trie node (assumed allocated itself). */
static int Tdup_trie(const Trie *t1, Trie *t2, value_t (*nval)(value_t), knot_mm_t *mm) {
	if (!isbranch(t1)) {
		Tkey *key1 = t1->leaf.key;
		Tkey *key2 = mm_alloc(mm, sizeof(Tkey) + key1->len);
		if (!key2)
			return KNOT_ENOMEM;
		key2->len = key1->len;
		memcpy(key2->chars, key1->chars, key1->len);
		t2->leaf.key = key2;
		t2->leaf.val = nval(t1->leaf.val);
		return 0;
	}
	memcpy(t2, t1, sizeof(Tbranch)); // flags etc.; will rewrite the pointer
	int child_count = popcount(t1->branch.bitmap);
	t2->branch.twigs = mm_alloc(mm, sizeof(Trie) * child_count);
	Trie *twigs1 = t1->branch.twigs;
	Trie *twigs2 = t2->branch.twigs;
	if (unlikely(!twigs2))
		return KNOT_ENOMEM;
	for (int i = 0; i < child_count; ++i) {
		int err = Tdup_trie(twigs1 + i, twigs2 + i, nval, mm);
		if (unlikely(err)) { // error: we need to free already allocated stuff
			while (--i >= 0)
				TfreeTrie(twigs2 + i, mm);
			return err;
		};
	}
	return 0;
}
Tbl* Tdup(const struct Tbl *tbl, value_t (*nval)(value_t)) {
	Tbl *t = mm_alloc(/*const-cast*/(knot_mm_t*) &tbl->mm, sizeof(Tbl));
	if (unlikely(!t))
		return NULL;
	t->mm = tbl->mm;
	if (!nval) {
		t->weight = 0;
		return t;
	}
	t->weight = tbl->weight;
	if (unlikely(!Tdup_trie(&tbl->root, &t->root, nval, &t->mm))) {
		Tfree(t);
		return NULL;
	};
	return t;
}


size_t Tweight(const struct Tbl *tbl) {
	return tbl ? tbl->weight : 0; // for some reason, HAT supports this on NULL
}

value_t* Tget_try(Tbl *tbl, const char *key, uint32_t len) {
	assert(tbl);
	if (!tbl->weight)
		return NULL;
	Trie *t = &tbl->root;
	while (isbranch(t)) {
		__builtin_prefetch(t->branch.twigs);
		Tbitmap b = twigbit(t, key, len);
		if (!hastwig(t, b))
			return NULL;
		t = twig(t, twigoff(t, b));
	}
	if (key_cmp(key, len, t->leaf.key->chars, t->leaf.key->len) != 0)
		return NULL;
	return &t->leaf.val;
}

// TODO: review
static bool next_rec(Trie *t, const char **pkey, uint32_t *plen, value_t **pval) {
	if(isbranch(t)) {
		// Recurse to find either this leaf (*pkey != NULL)
		// or the next one (*pkey == NULL).
		Tbitmap b = twigbit(t, *pkey, *plen);
		uint s, m; TWIGOFFMAX(s, m, t, b);
		for(; s < m; s++)
			if(next_rec(twig(t, s), pkey, plen, pval))
				return(true);
		return(false);
	}
	// We have found the next leaf.
	if(*pkey == NULL) {
		*pkey = t->leaf.key->chars;
		*plen = t->leaf.key->len;
		*pval = &t->leaf.val;
		return(true);
	}
	// We have found this leaf, so start looking for the next one.
	if(key_cmp(*pkey, *plen, t->leaf.key->chars, t->leaf.key->len) == 0) {
		*pkey = NULL;
		*plen = 0;
		return(false);
	}
	// No match.
	return(false);
}

// TODO: review
bool Tget_next(Tbl *tbl, const char **pkey, uint32_t *plen, value_t **pval) {
	if (tbl == NULL) {
		*pkey = NULL;
		*plen = 0;
		return(NULL);
	}
	return next_rec(&tbl->root, pkey, plen, pval);
}

bool Tdel(struct Tbl *tbl, const char *key, uint32_t len, value_t *pval) {
	assert(tbl);
	if (!tbl->weight)
		return false;
	Trie *t = &tbl->root; // current and parent node
	Tbranch *p = NULL;
	Tbitmap b = 0;
	while (isbranch(t)) {
		__builtin_prefetch(t->branch.twigs);
		b = twigbit(t, key, len);
		if (!hastwig(t, b))
			return false;
		p = &t->branch;
		t = twig(t, twigoff(t, b));
	}
	if (key_cmp(key, len, t->leaf.key->chars, t->leaf.key->len) != 0)
		return false;
	mm_free(&tbl->mm, t->leaf.key);
	if (pval != NULL)
		*pval = t->leaf.val; // we return value_t directly when deleting
	--tbl->weight;
	if (unlikely(!p)) { // whole trie was a single leaf
		assert(tbl->weight == 0);
		tbl->root = (Trie) { .leaf = { NULL, NULL } };
		return true;
	}
	// remove leaf t as child of p
	int ci = t - p->twigs, // child index via pointer arithmetic
	    cc = popcount(p->bitmap); // child count
	assert(ci >= 0 && ci < cc);

	if (cc == 2) { // collapse binary node p: move the other child to this node
		Trie *twigs = p->twigs;
		(*(Trie*)p) = twigs[1-ci]; // it might be a leaf or branch
		mm_free(&tbl->mm, twigs);
		return true;
	}
	memmove(p->twigs+ci, p->twigs+ci+1, sizeof(Trie) * (cc - ci - 1));
	p->bitmap &= ~b;
	Trie *twigs = mm_realloc(&tbl->mm,
			p->twigs, sizeof(Trie) * (cc - 1), sizeof(Trie) * cc);
	if (likely(twigs != NULL))
		p->twigs = twigs;
		/* We can ignore mm_realloc failure, only beware that next time
		 * the prev_size passed to it wouldn't be correct; TODO? */
	return true;
}

typedef struct TnodeStack {
	/* Notes:
	 * - malloc is used directly instead of mm */
	Trie* *stack;
	uint32_t len, alen;
	Trie* stack_init[2000 / sizeof(Trie*)]; // small enough but should fit most use cases
} TnodeStack;

/*! \brief Create a node stack containing just the root. */
static void Tns_init(TnodeStack *ns, struct Tbl *tbl) {
	assert(tbl);
	ns->stack = ns->stack_init;
	ns->len = 1;
	ns->alen = sizeof(ns->stack_init) / sizeof(ns->stack_init[0]);
	ns->stack[0] = &tbl->root;
}

static void Tns_cleanup(TnodeStack *ns) {
	assert(ns && ns->stack);
	if (likely(ns->stack == ns->stack_init))
		return;
	free(ns->stack);
	#ifndef NDEBUG
		ns->stack = NULL;
		ns->alen = 0;
	#endif
}

static int Tns_longer_alloc(TnodeStack *ns) {
	ns->alen *= 2;
	size_t new_size = sizeof(TnodeStack) + ns->alen * sizeof(Trie*);
	Trie* *st;
	if (ns->stack == ns->stack_init) {
		st = malloc(new_size);
		if (st != NULL)
			memcpy(st, ns->stack, ns->len * sizeof(Trie*));
	} else {
		st = realloc(ns->stack, new_size);
	}
	if (st == NULL)
		return KNOT_ENOMEM;
	ns->stack = st;
	return 0;
}
/*! \brief Ensure the node stack can be extended. */
static inline int Tns_longer(TnodeStack *ns) {
	// get a longer stack if needed
	if (likely(ns->len < ns->alen))
		return 0;
	return Tns_longer_alloc(ns); // hand-split the part suitable for inlining
}

/*! \brief Find the "branching point" as if searching for a key.
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
static int Tns_find_branch(TnodeStack *ns, const char *key, uint32_t len
		, Tbranch *pinfo, int *pfirst)
{
	assert(ns && ns->len && pinfo);
	// First find some leaf with longest matching prefix.
	while (isbranch(ns->stack[ns->len - 1])) {
		ERR_RETURN(Tns_longer(ns));
		Trie *t = ns->stack[ns->len - 1];
		__builtin_prefetch(t->branch.twigs);
		Tbitmap b = twigbit(t, key, len);
		// Even if our key is missing from this branch we need to
		// keep iterating down to a leaf. It doesn't matter which
		// twig we choose since the keys are all the same up to this
		// index. Note that blindly using twigoff(t, b) can cause
		// an out-of-bounds index if it equals twigmax(t).
		uint i = hastwig(t, b) ? twigoff(t, b) : 0;
		ns->stack[ns->len++] = twig(t, i);
	}
	Tkey *lkey = ns->stack[ns->len-1]->leaf.key;
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
	Tbranch *t;
	do {
		if (unlikely(ns->len == 1))
			goto success; // only the root stays on the stack
		t = (Tbranch*) ns->stack[ns->len-2];
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

/*! \brief Advance the node stack to the last leaf in the subtree.
 *
 *		Return 0 or KNOT_ENOMEM. */
static int Tns_last_leaf(TnodeStack *ns) {
	assert(ns);
	do {
		ERR_RETURN(Tns_longer(ns));
		Trie *t = ns->stack[ns->len - 1];
		if (!isbranch(t))
			return 0;
		int lasti = popcount(t->branch.bitmap) - 1;
		assert(lasti >= 0);
		ns->stack[ns->len++] = twig(t, lasti);
	} while (true);
}
/*! \brief Advance the node stack to the first leaf in the subtree.
 *
 *		Return 0 or KNOT_ENOMEM. */
static int Tns_first_leaf(TnodeStack *ns) {
	assert(ns);
	do {
		ERR_RETURN(Tns_longer(ns));
		Trie *t = ns->stack[ns->len - 1];
		if (!isbranch(t))
			return 0;
		ns->stack[ns->len++] = twig(t, 0);
	} while (true);
}

/*! \brief Advance the node stack to the leaf that is previous to the current node.
 *
 * Note: prefix leaf under the current node DOES count (if present; perhaps questionable).
 * Return 0 on success, 1 on not-found, or possibly KNOT_ENOMEM. */
static int Tns_prev_leaf(TnodeStack *ns) {
	assert(ns && ns->len > 0);

	Trie *t = ns->stack[ns->len-1];
	if (hastwig(t, 1<<0)) { // the prefix leaf
		t = twig(t, 0);
		ERR_RETURN(Tns_longer(ns));
		ns->stack[ns->len++] = t;
		return 0;
	}

	do {
		if (ns->len < 2)
			return 1; // root without empty key has no previous leaf
		t = ns->stack[ns->len-1];
		Trie *p = ns->stack[ns->len-2];
		int pindex = t - p->branch.twigs; // index in parent via pointer arithmetic
		assert(pindex >= 0 && pindex <= 16);
		if (pindex > 0) { // t isn't the first child -> go down the previous one
			ns->stack[ns->len-1] = twig(p, pindex-1);
			return Tns_last_leaf(ns);
		}
		// we've got to go up again
		--ns->len;
	} while (true);
}
/*! \brief Advance the node stack to the leaf that is successor to the current node.
 *
 * Note: prefix leaf or anything else under the current node DOES count.
 * Return 0 on success, 1 on not-found, or possibly KNOT_ENOMEM. */
static int Tns_next_leaf(TnodeStack *ns) {
	assert(ns && ns->len > 0);

	Trie *t = ns->stack[ns->len-1];
	if (isbranch(t))
		return Tns_first_leaf(ns);

	do {
		if (ns->len < 2)
			return 1; // not found, as no more parent is available
		t = ns->stack[ns->len-1];
		Trie *p = ns->stack[ns->len-2];
		int pindex = t - p->branch.twigs; // index in parent via pointer arithmetic
		assert(pindex >= 0 && pindex <= 16);
		int pcount = popcount(p->branch.bitmap);
		if (pindex+1 < pcount) { // t isn't the last child -> go down the next one
			ns->stack[ns->len-1] = twig(p, pindex+1);
			return Tns_first_leaf(ns);
		}
		// we've got to go up again
		--ns->len;
	} while (true);
}

int Tget_leq(struct Tbl *tbl, const char *key, uint32_t len, value_t **pval) {
	assert(tbl && pval);
	*pval = NULL; // so on failure we can just return 1;
	if (tbl->weight == 0)
		return 1;
	// First find a key with longest-matching prefix
	__attribute__((cleanup(Tns_cleanup)))
		TnodeStack ns_local;
	TnodeStack *ns = &ns_local;
	Tns_init(ns, tbl);
	Tbranch bp;
	int un_leaf; // first unmatched character in the leaf
	ERR_RETURN(Tns_find_branch(ns, key, len, &bp, &un_leaf));
	int un_key = bp.index < len ? key[bp.index] : -256;
	Trie *t = ns->stack[ns->len-1];
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
			ERR_RETURN(Tns_last_leaf(ns));
			goto success;
		}
		--ns->len;
		t = ns->stack[ns->len-1];
	}
	// Now we re-do the first "non-matching" step in the trie
	// but try the previous child if key was less (it may not exist)
	Tbitmap b = twigbit(t, key, len);
	int i = hastwig(t, b)
		? twigoff(t, b) - (un_key < un_leaf)
		: twigoff(t, b) - 1 /*twigoff returns successor when !hastwig*/;
	if (i >= 0) {
		ERR_RETURN(Tns_longer(ns));
		ns->stack[ns->len++] = twig(t, i);
		ERR_RETURN(Tns_last_leaf(ns));
	} else {
		ERR_RETURN(Tns_prev_leaf(ns)); // KNOT_ENOMEM or 1 for no-leq
	}
success:
	assert(!isbranch(ns->stack[ns->len-1]));
	*pval = & ns->stack[ns->len-1]->leaf.val;
	return -1;
}

/*! \brief Initialize a new leaf, copying the key, and returning failure code. */
static int mk_leaf(Trie *leaf, const char *key, uint32_t len, knot_mm_t *mm) {
	Tkey *k = mm_alloc(mm, sizeof(Tkey) + len);
	if (unlikely(!k))
		return KNOT_ENOMEM;
	k->len = len;
	memcpy(k->chars, key, len);
	leaf->leaf = (Tleaf){ .val = NULL, .key = k };
	return 0;
}

value_t* Tget_ins(struct Tbl *tbl, const char *key, uint32_t len) {
	assert(tbl);
	// First leaf in an empty tbl?
	if (unlikely(!tbl->weight)) {
		if (unlikely(mk_leaf(&tbl->root, key, len, &tbl->mm)))
			return NULL;
		++tbl->weight;
		return &tbl->root.leaf.val;
	}
	// Find the branching-point
	__attribute__((cleanup(Tns_cleanup)))
		TnodeStack ns_local;
	TnodeStack *ns = &ns_local;
	Tns_init(ns, tbl);
	Tbranch bp; // branch-point: index and flags signifying the longest common prefix
	int k2; // the first unmatched character in the leaf
	if (unlikely(Tns_find_branch(ns, key, len, &bp, &k2)))
		return NULL;
	Trie *t = ns->stack[ns->len - 1];
	if (bp.flags == 0) // the same key was already present
		return &t->leaf.val;
	Trie leaf;
	if (unlikely(mk_leaf(&leaf, key, len, &tbl->mm)))
		return NULL;

	if (isbranch(t) && bp.index == t->branch.index && bp.flags == t->branch.flags) {
		// The node t needs a new leaf child.
		Tbitmap b1 = twigbit(t, key, len);
		assert(!hastwig(t, b1));
		uint s, m; TWIGOFFMAX(s, m, t, b1); // new child position and original child count
		Trie *twigs = mm_realloc(&tbl->mm, t->branch.twigs,
				sizeof(Trie) * (m + 1), sizeof(Trie) * m);
		if (unlikely(!twigs))
			goto err_leaf;
		memmove(twigs+s+1, twigs+s, sizeof(Trie) * (m - s));
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
				Trie *pt = ns->stack[ns->len-2];
				assert(hastwig(pt, twigbit(pt, key, len)));
			}
		#endif
		Trie *twigs = mm_alloc(&tbl->mm, sizeof(Trie) * 2);
		if (unlikely(!twigs))
			goto err_leaf;
		Trie t2 = *t; // Save before overwriting t.
		t->branch = bp; // copy flags and index
		t->branch.twigs = twigs;
		Tbitmap b1 = twigbit(t, key, len);
		Tbitmap b2 = unlikely(k2 == -256) ? (1<<0) : nibbit(k2, bp.flags);
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
static int TapplyTrie(Trie *t, int (*f)(value_t*,void*), void* d) {
	assert(t);
	if (!isbranch(t))
		return f(&t->leaf.val, d);
	int child_count = popcount(t->branch.bitmap);
	for (int i = 0; i < child_count; ++i)
		ERR_RETURN(TapplyTrie(twig(t, i), f, d));
	return 0;
}
int Tapply(struct Tbl *tbl, int (*f)(value_t*,void*), void* d) {
	assert(tbl && f);
	if (!tbl->weight)
		return 0;
	return TapplyTrie(&tbl->root, f, d);
}

/* Tit_t is implemented via a simple TnodeStack,
 * always pointing to the current leaf, unless we've finished (i.e. it->len == 0).
 * These are all thin wrappers around static Tns* functions. */
Tit_t* Tit_begin(struct Tbl *tbl) {
	assert(tbl);
	Tit_t *it = malloc(sizeof(TnodeStack));
	if (!it)
		return NULL;
	Tns_init(it, tbl);
	if (Tns_first_leaf(it)) {
		Tns_cleanup(it);
		free(it);
		return NULL;
	}
	return it;
}
int Tit_next(Tit_t *it) {
	assert(it && it->len);
	int err = Tns_next_leaf(it);
	if (err == 1)
		it->len = 0; // just finished
	return err;
}
bool Tit_finished(Tit_t *it) {
	assert(it);
	return it->len == 0;
}
void Tit_free(Tit_t *it) {
	if (!it)
		return;
	Tns_cleanup(it);
	free(it);
}
const char* Tit_key(Tit_t *it, uint32_t *len) {
	assert(it && it->len);
	Trie *t = it->stack[it->len-1];
	assert(!isbranch(t));
	Tkey *key = t->leaf.key;
	if (len)
		*len = key->len;
	return key->chars;
}
value_t* Tit_val(Tit_t *it) {
	assert(it && it->len);
	Trie *t = it->stack[it->len-1];
	assert(!isbranch(t));
	return &t->leaf.val;
}

