/*
 * This file is part of hat-trie
 *
 * Copyright (c) 2011 by Daniel C. Jones <dcjones@cs.washington.edu>
 *
 * This is an ANSI C99 implementation of the HAT-trie data structure of Askitis
 * and Sinha, an extremely efficient (space and time) modern variant of tries.
 * The HAT-trie is in essence a hybrid data structure, combining tries and hash
 * tables in a clever way to try to get the best of both worlds.
 *
 * The version implemented here maps arrays of bytes to words (i.e., unsigned
 * longs), which can be used to store counts, pointers, etc, or not used at all if
 * you simply want to maintain a set of unique strings.
 *
 * For details see
 *  1. Askitis, N., & Sinha, R. (2007). HAT-trie: a cache-conscious trie-based data
 *     structure for strings. Proceedings of the thirtieth Australasian conference on
 *     Computer science-Volume 62 (pp. 97–105). Australian Computer Society, Inc.
 *  2. Askitis, N., & Zobel, J. (2005). Cache-conscious collision resolution in
 *     string hash tables. String Processing and Information Retrieval (pp.
 *     91–102). Springer.
 */

#pragma once

#ifdef __cplusplus
extern "C" {
#endif

#ifndef TRIE_USE_QP
    #define TRIE_USE_QP 1
#endif

#if TRIE_USE_QP

typedef struct Tbl hattrie_t;
typedef struct TnodeStack hattrie_iter_t;
// dummy
#define TRIE_BUCKET_SIZE (-1)
// FIXME: ../../../utils/knotc/estimator.c
#include "contrib/hhash.h"

#else

#include <stdlib.h>
#include <stdbool.h>

#include "contrib/hhash.h"

struct knot_mm;

/* Hat-trie defines. */
#define TRIE_ZEROBUCKETS  0    /* Do not use hash buckets (pure trie). */
#define TRIE_BUCKET_SIZE  253  /* 253, 509, 765 for n*4K pages per 1 hhash. */
#define TRIE_BUCKET_INCR  256  /* Size increase. */
#define TRIE_BUCKET_MAX   4    /* Maximum N table increments. */
#define TRIE_MAXCHAR      0xff /* Use 7-bit ASCII alphabet. */
#define TRIE_EOK          KNOT_EOK

typedef struct hattrie_t_ hattrie_t;
typedef struct hattrie_iter_t_ hattrie_iter_t;

#endif // #if TRIE_USE_QP

// the common part of interface
#include "contrib/hat-trie/hat-api.h"

#ifdef __cplusplus
}
#endif
