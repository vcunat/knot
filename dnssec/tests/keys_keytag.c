#include <tap/basic.h>
#include <stdint.h>

#include "binary.h"
#include "keys/keytag.h"

int main(void)
{
	plan_lazy();

	const dnssec_binary_t rsa_md5_rdata = { .size = 72, .data = (uint8_t []) {
		0x01, 0x00, 0x03, 0x01,
		0x03, 0x01, 0x00, 0x01, 0xa6, 0x83, 0x41, 0x42, 0x58, 0x1b,
		0xc2, 0xa7, 0xc7, 0xd5, 0xef, 0xb5, 0x6c, 0xec, 0x34, 0xc5,
		0xc9, 0x5e, 0x84, 0xa8, 0x35, 0x4a, 0xe0, 0xc2, 0x70, 0xf5,
		0x40, 0xe9, 0x92, 0x06, 0x70, 0x45, 0x88, 0xd3, 0x86, 0xcf,
		0xf5, 0xff, 0x83, 0x08, 0x06, 0x98, 0xe7, 0x8a, 0xa9, 0x2c,
		0xe7, 0xe1, 0x4d, 0xa6, 0x46, 0xef, 0x3a, 0x96, 0x93, 0x8c,
		0xc1, 0x02, 0x00, 0x6f, 0x31, 0x9f, 0xa2, 0x1d
	}};

	ok(keytag(&rsa_md5_rdata) == 40866, "keytag for RSA/MD5");

	const dnssec_binary_t ecdsa_rdata = { .size = 100, .data = (uint8_t []) {
		0x01, 0x00, 0x03, 0x0e,
		0xbe, 0x8f, 0x42, 0x92, 0x34, 0xa0, 0x06, 0x5f, 0x18, 0xa1,
		0x15, 0x01, 0x84, 0x50, 0x33, 0x1f, 0x44, 0xa2, 0xbb, 0x61,
		0x2a, 0xc8, 0x86, 0x9c, 0xf3, 0x4b, 0x2e, 0xf9, 0x63, 0xd1,
		0x81, 0x72, 0x56, 0x96, 0xc7, 0x67, 0x34, 0xa1, 0x55, 0xc2,
		0xf3, 0x1d, 0x03, 0xbe, 0x1b, 0x39, 0xeb, 0xa7, 0xb8, 0x2c,
		0x72, 0x2e, 0x58, 0x75, 0x56, 0x42, 0x0b, 0x6f, 0x21, 0xa2,
		0x33, 0xf4, 0x21, 0x00, 0xb7, 0x0f, 0x5a, 0xf7, 0x1a, 0xf0,
		0xe9, 0x94, 0xfa, 0x43, 0xb0, 0x4a, 0x48, 0xb8, 0x64, 0x89,
		0x7b, 0xc9, 0xe0, 0xf7, 0x97, 0x52, 0xf4, 0x85, 0x0f, 0xb4,
		0xf4, 0xfc, 0xe2, 0x10, 0xd4, 0x26
	}};

	ok(keytag(&ecdsa_rdata) == 61768, "keytag for ECDSA/SHA384");

	return 0;
}
