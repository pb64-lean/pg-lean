import Pg.Crypto.Hex
import Pg.Crypto.Sha256
import Pg.Crypto.Md5
import Pg.Crypto.Hmac
import Pg.Crypto.Pbkdf2
import Pg.Crypto.Base64

/-!
Known-answer tests: SHA-256 (FIPS 180-4), HMAC-SHA-256 (RFC 4231),
PBKDF2-HMAC-SHA-256 (published SHA-256 analogues of the RFC 6070 vectors),
MD5 (RFC 1321) + PostgreSQL's md5 password hash, base64 (RFC 4648), hex.
-/

open Pg.Crypto

def expect (cond : Bool) (msg : String) : IO Unit := do
  unless cond do throw (IO.userError msg)

def expectHex (got : ByteArray) (want : String) (label : String) : IO Unit := do
  let g := toHexLower got
  unless g == want do throw (IO.userError s!"{label}: got {g}, want {want}")

def s (str : String) : ByteArray := str.toUTF8

def bytes (n : Nat) (b : UInt8) : ByteArray := Id.run do
  let mut out := ByteArray.empty
  for _ in [0:n] do
    out := out.push b
  return out

def hx (str : String) : ByteArray := (ofHex? str).getD ByteArray.empty

def main : IO Unit := do
  -- SHA-256, FIPS 180-4 examples + block boundaries
  expectHex (sha256 (s ""))
    "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855" "sha256 empty"
  expectHex (sha256 (s "abc"))
    "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad" "sha256 abc"
  expectHex (sha256 (s "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq"))
    "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1" "sha256 448-bit"
  expectHex (sha256 (bytes 64 97))
    "ffe054fe7ae0cb6dc65c3af9b61d5209f439851db43d0ba5997337df154668eb" "sha256 one full block"
  expectHex (sha256 (bytes 1000000 97))
    "cdc76e5c9914fb9281a1c7e284d73e67f1809a48a497200e046d39ccc7112cd0" "sha256 million a"

  -- HMAC-SHA-256, RFC 4231 test cases 1-4, 6, 7
  expectHex (hmacSha256 (bytes 20 0x0b) (s "Hi There"))
    "b0344c61d8db38535ca8afceaf0bf12b881dc200c9833da726e9376c2e32cff7" "hmac tc1"
  expectHex (hmacSha256 (s "Jefe") (s "what do ya want for nothing?"))
    "5bdcc146bf60754e6a042426089575c75a003f089d2739839dec58b964ec3843" "hmac tc2"
  expectHex (hmacSha256 (bytes 20 0xaa) (bytes 50 0xdd))
    "773ea91e36800e46854db8ebd09181a72959098b3ef8c122d9635514ced565fe" "hmac tc3"
  expectHex (hmacSha256 (hx "0102030405060708090a0b0c0d0e0f10111213141516171819") (bytes 50 0xcd))
    "82558a389a443c0ea4cc819899f2083a85f0faa3e578f8077a2e3ff46729665b" "hmac tc4"
  expectHex (hmacSha256 (bytes 131 0xaa) (s "Test Using Larger Than Block-Size Key - Hash Key First"))
    "60e431591ee0b67f0d8a26aacbf5b77f8e0bc6213728c5140546040f0ee37f54" "hmac tc6"
  expectHex (hmacSha256 (bytes 131 0xaa)
      (s "This is a test using a larger than block-size key and a larger than block-size data. The key needs to be hashed before being used by the HMAC algorithm."))
    "9b09ffa71b942fcb27635fbcd5b0e944bfdc63644f0713938a7f51535c3a35e2" "hmac tc7"

  -- PBKDF2-HMAC-SHA-256
  expectHex (pbkdf2HmacSha256 (s "password") (s "salt") 1)
    "120fb6cffcf8b32c43e7225256c4f837a86548c92ccc35480805987cb70be17b" "pbkdf2 c=1"
  expectHex (pbkdf2HmacSha256 (s "password") (s "salt") 2)
    "ae4d0c95af6b46d32d0adff928f06dd02a303f8ef3c251dfd6e2d85a95474c43" "pbkdf2 c=2"
  expectHex (pbkdf2HmacSha256 (s "password") (s "salt") 4096)
    "c5e478d59288c841aa530db6845c4c8d962893a001ce4e11a4963873aa98134a" "pbkdf2 c=4096"
  expectHex (pbkdf2HmacSha256 (s "passwordPASSWORDpassword") (s "saltSALTsaltSALTsaltSALTsaltSALTsalt") 4096 40)
    "348c89dbcbd32b2f32d814b8116e84cf2b17347ebc1800181c4e2a1fb8dd53e1c635518c7dac47e9"
    "pbkdf2 multi-block"

  -- MD5, RFC 1321 appendix A.5 + PostgreSQL password hash
  expectHex (md5 (s "")) "d41d8cd98f00b204e9800998ecf8427e" "md5 empty"
  expectHex (md5 (s "a")) "0cc175b9c0f1b6a831c399e269772661" "md5 a"
  expectHex (md5 (s "abc")) "900150983cd24fb0d6963f7d28e17f72" "md5 abc"
  expectHex (md5 (s "message digest")) "f96b697d7cb7938d525a2f31aaf161d0" "md5 message digest"
  expectHex (md5 (s "abcdefghijklmnopqrstuvwxyz")) "c3fcd3d76192e4007dfb496cca67e13b" "md5 alphabet"
  expectHex (md5 (s "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789"))
    "d174ab98d277d9f5a5611c2c9f419d9f" "md5 alnum"
  expectHex (md5 (s "12345678901234567890123456789012345678901234567890123456789012345678901234567890"))
    "57edf4a22be3c955ac49da2e2107b67a" "md5 80 digits"
  expect (md5PasswordHash "bill" "secret" (hx "01020304") == "md5280f65115b55f033717cf14ca2f70630")
    "pg md5 password hash"

  -- base64, RFC 4648 §10
  let b64Cases : List (String × String) :=
    [("", ""), ("f", "Zg=="), ("fo", "Zm8="), ("foo", "Zm9v"),
     ("foob", "Zm9vYg=="), ("fooba", "Zm9vYmE="), ("foobar", "Zm9vYmFy")]
  for (plain, encoded) in b64Cases do
    expect (Base64.encode (s plain) == encoded) s!"b64 encode {plain}"
    expect ((Base64.decode? encoded).map toHexLower == some (toHexLower (s plain)))
      s!"b64 decode {encoded}"
  expect ((Base64.decode? "Zg==").map toHexLower == some "66") "b64 decode f"
  expect ((Base64.decode? "W22ZaJ0SNY7soEsUEjb6gQ==").isSome) "b64 decode scram salt"
  expect ((Base64.decode? "Zg=").isNone) "b64 reject length"
  expect ((Base64.decode? "Zg#=").isNone) "b64 reject char"
  expect ((Base64.decode? "Zm9=").isNone) "b64 reject non-canonical"
  expect ((Base64.decode? "Zg=x").isNone) "b64 reject digit after pad"
  -- binary roundtrip across all byte values
  let all := Id.run do
    let mut out := ByteArray.empty
    for i in [0:256] do
      out := out.push (UInt8.ofNat i)
    return out
  expect ((Base64.decode? (Base64.encode all)).map toHexLower == some (toHexLower all))
    "b64 roundtrip all bytes"

  -- hex
  expect (toHexLower (hx "00ff10ab") == "00ff10ab") "hex roundtrip"
  expect ((ofHex? "0F0f").map toHexLower == some "0f0f") "hex mixed case"
  expect ((ofHex? "abc").isNone) "hex odd length"
  expect ((ofHex? "zz").isNone) "hex bad digit"

  IO.println "all crypto assertions passed"
