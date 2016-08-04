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

#define ERR_RETURN(x) \
	do { \
		int err_code_ = x; \
		if (unlikely(err_code_)) \
			return err_code_; \
	} while (false)


// NOTE: 17 bits only; NARROW/SLOW maybe only supports 16
static uint popcount(Tbitmap w) {
	#if defined(HAVE_NARROW_CPU) || defined(HAVE_SLOW_POPCOUNT)
		w -= (w >> 1) & 0x5555;
		w = (w & 0x3333) + ((w >> 2) & 0x3333);
		w = (w + (w >> 4)) & 0x0F0F;
		w = (w + (w >> 8)) & 0x00FF;
		return(w);
	#else
		return((uint)__builtin_popcount(w));
	#endif
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
	uint len; // uint should be enough as the key length;
			// probably even 16 bits would be. TODO: apply everywhere?
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

// Test flags to determine type of this node.

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
static Tbitmap twigbit(Trie *t, const char *key, uint len) {
	assert(isbranch(t));
	uint i = t->branch.index;

	if (i >= len)
		return 1 << 0; // leaf position

	return nibbit((byte)key[i], t->branch.flags);
}

static bool hastwig(Trie *t, Tbitmap bit) {
	return t->branch.bitmap & bit;
}

static uint twigoff(Trie *t, Tbitmap b) {
	return popcount(t->branch.bitmap & (b-1));
}

static Trie* twig(Trie *t, uint i) {
	return &t->branch.twigs[i];
}

#ifdef HAVE_NARROW_CPU

#define TWIGOFFMAX(off, max, t, b) do {				\
		Tbitmap bitmap = t->branch.bitmap;		\
		uint word = (bitmap << 16) | (bitmap & (b-1));	\
		uint counts = popcount16x2(word);		\
		off = counts & 0xFF;				\
		max = (counts >> 16) & 0xFF;			\
	} while(0)

#else

#define TWIGOFFMAX(off, max, t, b) do {			\
		off = twigoff(t, b);			\
		max = popcount(t->branch.bitmap);	\
	} while(0)

#endif

/*! \brief Item comparator from hhash.c */
static int key_cmp(const char *k1, uint k1_len, const char *k2, uint k2_len)
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
	t->weight = tbl->weight;
	t->mm = tbl->mm;
	if (unlikely(!Tdup_trie(&tbl->root, &t->root, nval, &t->mm))) {
		Tfree(t);
		return NULL;
	};
	return t;
}


size_t Tweight(const struct Tbl *tbl) {
	return tbl->weight;
}

value_t* Tget_try(Tbl *tbl, const char *key, size_t klen) {
	assert(tbl);
	if (!tbl->weight)
		return NULL;
	Trie *t = &tbl->root;
	while (isbranch(t)) {
		__builtin_prefetch(t->branch.twigs);
		Tbitmap b = twigbit(t, key, klen);
		if (!hastwig(t, b))
			return NULL;
		t = twig(t, twigoff(t, b));
	}
	if (key_cmp(key, klen, t->leaf.key->chars, t->leaf.key->len) != 0)
		return NULL;
	return &t->leaf.val;
}

// TODO: review
static bool next_rec(Trie *t, const char **pkey, size_t *plen, value_t **pval) {
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
bool Tget_next(Tbl *tbl, const char **pkey, size_t *plen, value_t **pval) {
	if (tbl == NULL) {
		*pkey = NULL;
		*plen = 0;
		return(NULL);
	}
	return next_rec(&tbl->root, pkey, plen, pval);
}

bool Tdel(struct Tbl *tbl, const char *key, size_t len, value_t *pval) {
	assert(tbl);
	Trie *t = &tbl->root, *p = NULL; // current and parent pointers
	Tbitmap b = 0;
	while (isbranch(t)) {
		__builtin_prefetch(t->branch.twigs);
		b = twigbit(t, key, len);
		if (!hastwig(t, b))
			return false;
		p = t; t = twig(t, twigoff(t, b));
	}
	if (key_cmp(key, len, t->leaf.key->chars, t->leaf.key->len) != 0)
		return false;
	mm_free(&tbl->mm, t->leaf.key);
	if (pval != NULL)
		*pval = t->leaf.val; // we return value_t directly when deleting
	--tbl->weight;
	if (p == NULL) { // whole trie was a single leaf
		assert(tbl->weight == 0);
		tbl->root = (Trie) { .leaf = { NULL, NULL } };
		return true;
	} else {
		assert(tbl->weight > 0);
	}
	t = p; p = NULL; // Becuase t is the usual name
	uint s, m; TWIGOFFMAX(s, m, t, b);
	if (m == 2) { // collapse a binary node: move the other child to this node
		Trie *twigs = t->branch.twigs;
		*t = *twig(t, !s);
		mm_free(&tbl->mm, twigs);
		return true;
	}
	memmove(t->branch.twigs+s, t->branch.twigs+s+1, sizeof(Trie) * (m - s - 1));
	t->branch.bitmap &= ~b;
	// We have now correctly removed the twig from the trie, so if
	// realloc() fails we can ignore it and continue to use the
	// slightly oversized twig array.
	Trie *twigs = mm_realloc(&tbl->mm,
			t->branch.twigs, sizeof(Trie) * (m - 1), sizeof(Trie) * m);
	if (twigs != NULL)
		t->branch.twigs = twigs;
	return true;
}

typedef struct TnodeStack {
	/* Notes:
	 * - malloc is used directly instead of mm */
	Trie* *stack;
	uint len, alen;
	Trie* stack_init[];
} TnodeStack;

/*! \brief Create a node stack containing just the root. */
static TnodeStack * Tns_create(struct Tbl *tbl) {
	assert(tbl);
	//int log2 = sizeof(unsigned long)*8 - __builtin_clzl(hint+1);
	int alen = 2000 / sizeof(Trie*); // small enough but should fit most use cases
	TnodeStack *ns = malloc(sizeof(TnodeStack) + alen * sizeof(Trie*));
	ns->stack = ns->stack_init;
	ns->len = 1;
	ns->alen = alen;
	ns->stack[0] = &tbl->root;
	return ns;
}

static void Tns_free(TnodeStack *ns) {
	if (!ns)
		return;
	if (ns->stack != ns->stack_init)
		free(ns->stack);
	free(ns);
}
/* Wrapper suitable for __attribute__((cleanup)). */
static void Tns_free_cl(TnodeStack **ns) {
	Tns_free(*ns);
	*ns = NULL;
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

/*! \brief Find the branch-point as if searching for a key (leaf if found).
 *
 *  The whole path to the point is kept on the passed stack.
 *  If exact match is found, the corresponding leaf is left on top of the stack;
 *  otherwise a branch is on the top.
 *  \param pmlen Set the number of matched bytes, optionally.
 *  \param pkcmp Set the comparison status to the non-matching leaf, optionally,
 *    (char difference) signifying whether the first non-matching step in the trie
 *    was to a lexicographically greater (pkcmp > 0) or smaller (< 0) subtree.
 *    (The past-end-of-string character is considered to have value -256 for this.)
 *  Return 0 or KNOT_ENOMEM. */
static int Tns_find_branch(TnodeStack *ns, const char *key, size_t len
		, uint *pmlen, int *pkcmp)
{
	assert(ns && ns->len);
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
	// Find mlen: index of the first char that differs.
	uint mlen = 0;
	while (mlen < MIN(len,lkey->len)) {
		if (key[mlen] != lkey->chars[mlen])
			break;
		else
			++mlen;
	}
	if (pmlen)
		*pmlen = mlen;
	if (mlen == len && len == lkey->len) { // found equivalent key
		if (pkcmp)
			*pkcmp = 0;
		return 0;
	}
	// Find the half-byte part of matched length.
	uint f;
	//Tbitmap b1;
	if (likely(mlen < len)) {
		assert(mlen < lkey->len);
		byte k2 = (byte)lkey->chars[mlen];
		byte k1 = (byte)key[mlen];
		f = ((k1 ^ k2) & 0xf0) ? 1 : 2;
		if (pkcmp)
			*pkcmp = key[mlen] - lkey->chars[mlen];
		//b1 = nibbit(k1, f);
	} else { // mlen == len: searched key is a prefix of some stored key(s)
		f = 1;
		//b1 = 1<<0;
		if (pkcmp)
			*pkcmp = (-256) - lkey->chars[mlen];
		return 0;
	}
	// now go up the trie from the current leaf
	Tbranch *t;
	do {
		--ns->len;
		t = (Tbranch*) ns->stack[ns->len-1];
	} while (t->index > mlen || (t->index == mlen && t->flags > f));
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

int Tget_leq(struct Tbl *tbl, const char *key, size_t len, value_t **pval) {
	assert(tbl && pval);
	if (tbl->weight == 0)
		return 1;
	// First find a key with longest-matching prefix
	__attribute__((cleanup(Tns_free_cl)))
		TnodeStack *ns = Tns_create(tbl);
	int first_diff;
	ERR_RETURN(Tns_find_branch(ns, key, len, NULL, &first_diff));
	assert(ns->len > 0); // there should be the root at least
	Trie *t = ns->stack[ns->len-1];
	if (!isbranch(t)) { // found exact match
		if (pval)
			*pval = &t->leaf.val;
		return 0;
	}
	// Now we re-do the first "non-matching" step in the trie
	// but try the previous child if key was less (it may not exist)
	Tbitmap b = twigbit(t, key, len);
	int i = twigoff(t, b) - (first_diff < 0);
	if (i >= 0) {
		ERR_RETURN(Tns_longer(ns));
		ns->stack[ns->len++] = twig(t, i);
		ERR_RETURN(Tns_last_leaf(ns));
	} else {
		ERR_RETURN(Tns_prev_leaf(ns)); // KNOT_ENOMEM or 1 for no-leq
	}
	assert(!isbranch(ns->stack[ns->len-1]));
	*pval = & ns->stack[ns->len-1]->leaf.val;
	return -1;
}


/*! \brief Find a longest-prefix matching leaf, and optionally return the matching length. */
static Tleaf* Tfind_prefix_leaf(struct Tbl *tbl, const char *key, size_t len, uint *mlen) {
	assert(tbl);
	// Find the most similar leaf node in the trie. We will compare
	// its key with our new key to find the first differing nibble,
	// which can be at a lower index than the point at which we
	// detect a difference.
	Trie *t = &tbl->root;
	while (isbranch(t)) {
		__builtin_prefetch(t->branch.twigs);
		Tbitmap b = twigbit(t, key, len);
		// Even if our key is missing from this branch we need to
		// keep iterating down to a leaf. It doesn't matter which
		// twig we choose since the keys are all the same up to this
		// index. Note that blindly using twigoff(t, b) can cause
		// an out-of-bounds index if it equals twigmax(t).
		uint i = hastwig(t, b) ? twigoff(t, b) : 0;
		t = twig(t, i);
	}
	Tkey *tkey = t->leaf.key;
	if (mlen) {
		// Find i: index of the first char that differs.
		uint i = 0;
		while (i < MIN(len,tkey->len)) {
			if (key[i] != tkey->chars[i])
				break;
			else
				++i;
		}
		*mlen = i;
	}
	return &t->leaf;
}

value_t* Tget_ins(struct Tbl *tbl, const char *key, size_t len) {
	assert(tbl);
	// First leaf in an empty tbl?
	if (!tbl->weight) {
		++tbl->weight;
		tbl->root.leaf = (Tleaf) {
			.val = NULL,
			.key = mm_alloc(&tbl->mm, sizeof(Tkey)+len)
		};
		Tkey *nkey = tbl->root.leaf.key;
		if (nkey == NULL)
			return NULL;
		nkey->len = len;
		memcpy(nkey->chars, key, len);
		return &tbl->root.leaf.val;
	}
	uint mlen;
	Tleaf *tl = Tfind_prefix_leaf(tbl, key, len, &mlen);
	if (mlen == len && len == tl->key->len) // found equivalent key
		return &tl->val;
	// We have the branch's index; what are its flags?
	uint f;
	Tbitmap b1;
	byte k2 = (byte)tl->key->chars[mlen];
	if (likely(mlen < len)) {
		byte k1 = (byte)key[mlen];
		f = ((k1 ^ k2) & 0xf0) ? 1 : 2;
		b1 = nibbit(k1, f);
	} else { // mlen == len: inserted key is a prefix of some stored key(s)
		f = 1;
		b1 = 1<<0;
	}
	// Prepare the new leaf.
	Tkey *t1key = mm_alloc(&tbl->mm, sizeof(Tkey)+len);
	if (t1key == NULL)
		return NULL;
	t1key->len = len;
	memcpy(t1key->chars, key, len);
	Trie t1 = { .leaf = { .key = t1key, .val = NULL } };
	// Find where to insert a branch or grow an existing branch.
	Trie *t = &tbl->root;
	// TODO: this re-search might be skipped in most cases if we saved last one or two branches before
	while (isbranch(t)) {
		//__builtin_prefetch(t->branch.twigs); // we just passed them; should be cached
		if (mlen == t->branch.index && f == t->branch.flags)
			goto growbranch;
		if (mlen == t->branch.index && f < t->branch.flags)
			goto newbranch;
		if (mlen < t->branch.index)
			goto newbranch;
		Tbitmap b = twigbit(t, key, len);
		assert(hastwig(t, b));
		t = twig(t, twigoff(t, b));
	}
newbranch:;
	Trie *twigs = mm_alloc(&tbl->mm, sizeof(Trie) * 2);
	if (twigs == NULL)
		return NULL;
	Trie t2 = *t; // Save before overwriting.
	Tbitmap b2 = nibbit(k2, f);
	t->branch.twigs = twigs;
	t->branch.flags = f;
	t->branch.index = mlen;
	t->branch.bitmap = b1 | b2;
	*twig(t, twigoff(t, b1)) = t1;
	*twig(t, twigoff(t, b2)) = t2;
	++tbl->weight;
	return &twig(t, twigoff(t, b1))->leaf.val;
growbranch:;
	assert(!hastwig(t, b1));
	uint s, m; TWIGOFFMAX(s, m, t, b1);
	twigs = mm_realloc(&tbl->mm, t->branch.twigs, sizeof(Trie) * (m + 1), sizeof(Trie) * m);
	if (twigs == NULL) // TODO: I'm not completely certain this is correct if OOM
		return NULL;
	memmove(twigs+s+1, twigs+s, sizeof(Trie) * (m - s));
	memcpy(twigs+s, &t1, sizeof(Trie));
	t->branch.twigs = twigs;
	t->branch.bitmap |= b1;
	++tbl->weight;
	return &(twigs+s)->leaf.val;
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
 * always pointing to the current leaf, unless we've finished (and ns->len == 0).
 * These are all thin wrappers around static Tns* functions. */
Tit_t* Tit_begin(struct Tbl *tbl) {
	assert(tbl);
	Tit_t *it = Tns_create(tbl);
	if (Tns_first_leaf(it)) {
		Tns_free(it);
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
	return it->len == 0;
}
void Tit_free(Tit_t *it) {
	Tns_free(it);
}
const char* Tit_key(Tit_t *it, size_t *len) {
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

