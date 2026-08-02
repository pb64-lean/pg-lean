# TLS 1.3 CertificateVerify fixtures

These OpenSSL 3.6.2 certificates provide RSA-2048 (`rsaEncryption` SPKI),
P-256, and Ed25519 leaf keys for the hermetic sans-I/O TLS tests. The
corresponding private keys were used once to sign deterministic
CertificateVerify inputs and then deleted. Only public certificates and the
captured signatures in `Test/TlsTest.lean` are committed.

Each signed input is exactly:

```text
64 * 0x20 || "TLS 1.3, server CertificateVerify" || 0x00 ||
SHA256(ClientHello || ServerHello || EncryptedExtensions || Certificate)
```

The captured transcript hashes are:

```text
RSA-PSS-RSAE                 368c513aa3d01a41d9fc4a8da5719b1a97d7dde25a08dc99f43637239d36ba82
ECDSA-P256                   bb2c338022742ce6e43e99f959f18a3a69b22510654c139069d2b159dc7fb866
Ed25519                      3352d1586a02a02145b4a28363fbb06a520b69ee6496df910a53f844b0010958
Ed25519, empty session ID    a40e84207b92becf29dbfe44f55a2991d81960413db3ae6899c695f8cb2ca873
Ed25519, P-256 key exchange d9ca90f7686b9d776991ee32eaca1c769f1177ffe0557ac59c5c48e446a2224b
```

Certificates were generated with `openssl genpkey` followed by
`openssl req -new -x509`, fixed serials `0x4001` through `0x4003`, and critical
`CA:FALSE` BasicConstraints plus `digitalSignature` KeyUsage. After writing
each 130-byte signed input to `content.bin`, signatures were produced with:

```sh
openssl dgst -sha256 -sign rsa.key \
  -sigopt rsa_padding_mode:pss \
  -sigopt rsa_pss_saltlen:32 \
  -sigopt rsa_mgf1_md:sha256 \
  -out signature.bin content.bin

openssl dgst -sha256 -sign p256.key \
  -out signature.bin content.bin

openssl pkeyutl -sign -rawin -inkey ed25519.key \
  -in content.bin -out signature.bin
```

All five captures were independently verified with the matching OpenSSL
public key before the private keys were removed.
