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
 */

#include <stdlib.h>

#include "contrib/wire_ctx.h"
#include "libknot/errcode.h"
#include "libknot/rrtype/opt.h"
#include "libknot/rrtype/opt-cookie.h"

#define cookie_len_ok(clen) \
	(((clen) == KNOT_OPT_COOKIE_CLNT) || \
	 ((clen) >= (KNOT_OPT_COOKIE_CLNT + KNOT_OPT_COOKIE_SRVR_MIN) && \
	  (clen) <= (KNOT_OPT_COOKIE_CLNT + KNOT_OPT_COOKIE_SRVR_MAX)))

#define ccookie_len_ok(cclen) \
	((cclen) == KNOT_OPT_COOKIE_CLNT)

#define scookie_len_ok(sclen) \
	(((sclen) == 0) || \
	 ((sclen) >= KNOT_OPT_COOKIE_SRVR_MIN && \
	  (sclen) <= KNOT_OPT_COOKIE_SRVR_MAX))

_public_
uint16_t knot_edns_opt_cookie_data_len(uint16_t clen, uint16_t slen)
{
	return (ccookie_len_ok(clen) && scookie_len_ok(slen)) ? (clen + slen) : 0;
}

_public_
uint16_t knot_edns_opt_cookie_write(const uint8_t *cc, uint16_t cc_len,
                                    const uint8_t *sc, uint16_t sc_len,
                                    uint8_t *data, uint16_t data_len)
{
	if ((cc == NULL && cc_len > 0) || (sc == NULL && sc_len > 0)) {
		return 0;
	}

	if (data == NULL || data_len == 0) {
		return 0;
	}

	uint16_t cookies_size = knot_edns_opt_cookie_data_len(cc_len, sc_len);
	if (cookies_size == 0 || data_len < cookies_size) {
		return 0;
	}

	wire_ctx_t wire = wire_ctx_init(data, data_len);
	wire_ctx_write(&wire, cc, cc_len);
	if (sc_len > 0) {
		wire_ctx_write(&wire, sc, sc_len);
	}

	if (wire.error != KNOT_EOK) {
		return 0;
	}

	return wire_ctx_offset(&wire);
}

_public_
int knot_edns_opt_cookie_parse(const uint8_t *data, uint16_t data_len,
                               const uint8_t **cc, uint16_t *cc_len,
                               const uint8_t **sc, uint16_t *sc_len)
{
	if (data == NULL) {
		return KNOT_EINVAL;
	}

	if (!cookie_len_ok(data_len)) {
		return KNOT_EMALF;
	}

	if (cc != NULL && cc_len != NULL) {
		*cc_len = KNOT_OPT_COOKIE_CLNT;
		*cc = data;
	}

	if (sc != NULL && sc_len != NULL) {
		*sc_len = data_len - KNOT_OPT_COOKIE_CLNT;
		*sc = (*sc_len == 0) ? NULL : (data + KNOT_OPT_COOKIE_CLNT);
	}

	return KNOT_EOK;
}
