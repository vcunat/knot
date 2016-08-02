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





typedef unsigned char byte;
typedef unsigned int uint;

typedef uint Tbitmap;



// NOTE: 16 bits only
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
// 1 -> node is a branch, testing upper nibble
// 2 -> node is a branch, testing lower nibble
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
	union Trie *twigs;
	uint64_t
		flags : 2,
		index : 46,
		bitmap : 16;
	/* TODO: other than x86_64 ABI might be broken.
	 * > The order of bit fields within an allocation unit is undefined by standard!
	 * http://en.cppreference.com/w/c/language/bit_field
	 * but it's in ABI
	 * https://gcc.gnu.org/onlinedocs/gcc-6.1.0/gcc/Structures-unions-enumerations-and-bit-fields-implementation.html#Structures-unions-enumerations-and-bit-fields-implementation
	 * http://www.x86-64.org/documentation/abi.pdf (pg. 13,14)
	 * */
} Tbranch;

typedef union Trie {
	struct Tleaf   leaf;
	struct Tbranch branch;
} Trie;

typedef struct Tbl {
	union Trie root; // undefined when weight == 0, preferably all zeroed
	size_t weight;
	knot_mm_t mm;
} Tbl;

// Test flags to determine type of this node.

static bool isbranch(Trie *t) {
	return t->branch.flags != 0;
}

// Make a bitmask for testing a branch bitmap.
//
// mask:
// 1 -> 0xffff -> 0xfff0 -> 0xf0
// 2 -> 0x0000 -> 0x000f -> 0x0f
//
// shift:
// 1 -> 1 -> 4
// 2 -> 0 -> 0

static Tbitmap nibbit(byte k, uint flags) {
	uint mask = ((flags - 2) ^ 0x0f) & 0xff;
	uint shift = (2 - flags) << 2;
	return(1 << ((k & mask) >> shift));
}

// Extract a nibble from a key and turn it into a bitmask.
static Tbitmap twigbit(Trie *t, const char *key, size_t len) {
	uint64_t i = t->branch.index;
	if (i >= len)
		return 1;
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
	*trie = (Tbl) { .root = { .leaf = { NULL, NULL } }, .weight = 0, .mm = *mm };
	return trie;
}

void Tfree(struct Tbl *tbl) {
	abort();
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

bool Tget_next(Tbl *tbl, const char **pkey, size_t *plen, value_t **pval) {
	if (tbl == NULL) {
		*pkey = NULL;
		*plen = 0;
		return(NULL);
	}
	return next_rec(&tbl->root, pkey, plen, pval);
}

Tbl* Tdelkv(Tbl *tbl, const char *key, size_t len, const char **pkey, void **pval) {
	if(tbl == NULL)
		return(NULL);
	Trie *t = &tbl->root, *p = NULL;
	Tbitmap b = 0;
	while(isbranch(t)) {
		__builtin_prefetch(t->branch.twigs);
		b = twigbit(t, key, len);
		if(!hastwig(t, b))
			return(tbl);
		p = t; t = twig(t, twigoff(t, b));
	}
	if (key_cmp(key, len, t->leaf.key->chars, t->leaf.key->len) != 0)
		return(tbl);
	*pkey = t->leaf.key->chars;
	*pval = t->leaf.val;
	if(p == NULL) {
		free(tbl);
		return(NULL);
	}
	t = p; p = NULL; // Becuase t is the usual name
	uint s, m; TWIGOFFMAX(s, m, t, b);
	if(m == 2) {
		// Move the other twig to the parent branch.
		Trie *twigs = t->branch.twigs;
		*t = *twig(t, !s);
		free(twigs);
		return(tbl);
	}
	memmove(t->branch.twigs+s, t->branch.twigs+s+1, sizeof(Trie) * (m - s - 1));
	t->branch.bitmap &= ~b;
	// We have now correctly removed the twig from the trie, so if
	// realloc() fails we can ignore it and continue to use the
	// slightly oversized twig array.
	Trie *twigs = realloc(t->branch.twigs, sizeof(Trie) * (m - 1));
	if(twigs != NULL) t->branch.twigs = twigs;
	return(tbl);
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
	// Find the most similar leaf node in the trie. We will compare
	// its key with our new key to find the first differing nibble,
	// which can be at a lower index than the point at which we
	// detect a difference.
	Trie *t = &tbl->root;
	while(isbranch(t)) {
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
	// Find i: index of the first char that differs.
	uint i = 0;
	while (i < MIN(len,tkey->len)) {
		if (key[i] != tkey->chars[i])
			break;
		else
			++i;
	}
	if (i-1 == len && len == tkey->len) // found equivalent key
		return &t->leaf.val;
	// We have the branch's index; what are its flags?
	byte k1 = (byte)key[i], k2 = (byte)tkey->chars[i];
	uint f =  k1 ^ k2;
	f = (f & 0xf0) ? 1 : 2;
	// Prepare the new leaf.
	Tbitmap b1 = nibbit(k1, f);
	Tkey *t1key = mm_alloc(&tbl->mm, sizeof(Tkey)+len);
	if (t1key == NULL)
		return NULL;
	t1key->len = len;
	memcpy(t1key->chars, key, len);
	Trie t1 = { .leaf = { .key = t1key, .val = NULL } };
	// Find where to insert a branch or grow an existing branch.
	t = &tbl->root;
	while (isbranch(t)) {
		__builtin_prefetch(t->branch.twigs);
		if (i == t->branch.index && f == t->branch.flags)
			goto growbranch;
		if (i == t->branch.index && f < t->branch.flags)
			goto newbranch;
		if (i < t->branch.index)
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
	t->branch.index = i;
	t->branch.bitmap = b1 | b2;
	*twig(t, twigoff(t, b1)) = t1;
	*twig(t, twigoff(t, b2)) = t2;
	return &twig(t, twigoff(t, b1))->leaf.val;
growbranch:;
	assert(!hastwig(t, b1));
	uint s, m; TWIGOFFMAX(s, m, t, b1);
	twigs = mm_realloc(&tbl->mm, t->branch.twigs, sizeof(Trie) * (m + 1), sizeof(Trie) * m);
	if (twigs == NULL) // TODO: I'm not completely certain this is correct if OOM
		return NULL;
	memmove(twigs+s+1, twigs+s, sizeof(Trie) * (m - s));
	memmove(twigs+s, &t1, sizeof(Trie));
	t->branch.twigs = twigs;
	t->branch.bitmap |= b1;
	return &(twigs+s)->leaf.val;
}
