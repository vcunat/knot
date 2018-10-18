/*  Copyright (C) 2017-2018 CZ.NIC, z.s.p.o. <knot-dns@labs.nic.cz>

    This program is free software: you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.

    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with this program.  If not, see <https://www.gnu.org/licenses/>.
 */

#include <assert.h>
#include <stdlib.h>

#include "contrib/mempattern.h"
#include "contrib/string.h"
#include "contrib/ucw/mempool.h"

static void mm_nofree(void *p)
{
	/* nop */
}

void *mm_alloc(knot_mm_t *mm, size_t size)
{
	if (mm) {
		return mm->krealloc(mm->ctx, NULL, size, -1);
	} else {
		return malloc(size);
	}
}

void *mm_calloc(knot_mm_t *mm, size_t nmemb, size_t size)
{
	if (nmemb == 0 || size == 0) {
		return NULL;
	}
	if (mm) {
		size_t total_size = nmemb * size;
		if (total_size / nmemb != size) { // Overflow check
			return NULL;
		}
		void *mem = mm_alloc(mm, total_size);
		if (mem == NULL) {
			return NULL;
		}
		return memzero(mem, total_size);
	} else {
		return calloc(nmemb, size);
	}
}

void *mm_realloc(knot_mm_t *mm, void *what, size_t size, size_t prev_size)
{
	if (mm) {
		return mm->krealloc(mm->ctx, what, size, prev_size);
	} else {
		return realloc(what, size);
	}
}

static void *mm_mp_realloc(void *ctx, void *what, size_t size, size_t prev_size)
{
	if (what && size <= prev_size) {
		/* No use to decrease size with mempools. */
		return what;
	}
	void *p = mp_alloc(ctx, size);
	if (p == NULL) {
		return NULL;
	}
	if (what) {
		assert(prev_size <= size);
		memcpy(p, what, prev_size);
	}
	/* freeing is no-op */
	return p;
}

char *mm_strdup(knot_mm_t *mm, const char *s)
{
	if (s == NULL) {
		return NULL;
	}
	if (mm) {
		size_t len = strlen(s) + 1;
		void *mem = mm_alloc(mm, len);
		if (mem == NULL) {
			return NULL;
		}
		return memcpy(mem, s, len);
	} else {
		return strdup(s);
	}
}

void mm_free(knot_mm_t *mm, const void *what)
{
	if (mm) {
		if (mm->kfree) {
			mm->kfree((void *)what);
		}
	} else {
		free((void *)what);
	}
}

void mm_ctx_init(knot_mm_t *mm)
{
	memset(mm, 0, sizeof(*mm));
}

void mm_ctx_mempool(knot_mm_t *mm, size_t chunk_size)
{
	mm->ctx = mp_new(chunk_size);
	mm->krealloc = mm_mp_realloc;
	mm->kfree = mm_nofree;
}
