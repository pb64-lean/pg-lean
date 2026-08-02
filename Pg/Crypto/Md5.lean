module

public import Pg.Crypto.Hex

public section

namespace Pg
namespace Crypto

/-!
MD5 (RFC 1321), pure Lean. Cryptographically broken, but still required for
PostgreSQL's legacy `md5` password authentication (removed as a default in
PostgreSQL 18, still common on 17): the client sends
`"md5" ++ hex(md5(hex(md5(password ++ user)) ++ salt))`.
-/

private def rotl32 (x : UInt32) (n : UInt32) : UInt32 :=
  (x <<< n) ||| (x >>> (32 - n))

private def kMd5 : Array UInt32 := #[
  0xd76aa478, 0xe8c7b756, 0x242070db, 0xc1bdceee, 0xf57c0faf, 0x4787c62a, 0xa8304613, 0xfd469501,
  0x698098d8, 0x8b44f7af, 0xffff5bb1, 0x895cd7be, 0x6b901122, 0xfd987193, 0xa679438e, 0x49b40821,
  0xf61e2562, 0xc040b340, 0x265e5a51, 0xe9b6c7aa, 0xd62f105d, 0x02441453, 0xd8a1e681, 0xe7d3fbc8,
  0x21e1cde6, 0xc33707d6, 0xf4d50d87, 0x455a14ed, 0xa9e3e905, 0xfcefa3f8, 0x676f02d9, 0x8d2a4c8a,
  0xfffa3942, 0x8771f681, 0x6d9d6122, 0xfde5380c, 0xa4beea44, 0x4bdecfa9, 0xf6bb4b60, 0xbebfbc70,
  0x289b7ec6, 0xeaa127fa, 0xd4ef3085, 0x04881d05, 0xd9d4d039, 0xe6db99e5, 0x1fa27cf8, 0xc4ac5665,
  0xf4292244, 0x432aff97, 0xab9423a7, 0xfc93a039, 0x655b59c3, 0x8f0ccc92, 0xffeff47d, 0x85845dd1,
  0x6fa87e4f, 0xfe2ce6e0, 0xa3014314, 0x4e0811a1, 0xf7537e82, 0xbd3af235, 0x2ad7d2bb, 0xeb86d391]

private def sMd5 : Array UInt32 := #[
  7, 12, 17, 22, 7, 12, 17, 22, 7, 12, 17, 22, 7, 12, 17, 22,
  5, 9, 14, 20, 5, 9, 14, 20, 5, 9, 14, 20, 5, 9, 14, 20,
  4, 11, 16, 23, 4, 11, 16, 23, 4, 11, 16, 23, 4, 11, 16, 23,
  6, 10, 15, 21, 6, 10, 15, 21, 6, 10, 15, 21, 6, 10, 15, 21]

/-- Padding as in SHA-256 except the 64-bit bit length is little-endian. -/
private def padMd5 (msg : ByteArray) : ByteArray := Id.run do
  let bitLen : UInt64 := (UInt64.ofNat msg.size) * 8
  let mut data := msg.push 0x80
  let zeros := (64 + 56 - (msg.size + 1) % 64) % 64
  for _ in [0:zeros] do
    data := data.push 0
  for i in [0:8] do
    data := data.push (bitLen >>> (UInt64.ofNat (i * 8))).toUInt8
  return data

def md5 (msg : ByteArray) : ByteArray := Id.run do
  let data := padMd5 msg
  let mut a0 : UInt32 := 0x67452301
  let mut b0 : UInt32 := 0xefcdab89
  let mut c0 : UInt32 := 0x98badcfe
  let mut d0 : UInt32 := 0x10325476
  for blk in [0:data.size / 64] do
    let base := blk * 64
    let mut m : Array UInt32 := Array.empty
    for t in [0:16] do
      let o := base + t * 4
      m := m.push <|
        (data.get! o).toUInt32 |||
        (data.get! (o + 1)).toUInt32 <<< 8 |||
        (data.get! (o + 2)).toUInt32 <<< 16 |||
        (data.get! (o + 3)).toUInt32 <<< 24
    let mut a := a0
    let mut b := b0
    let mut c := c0
    let mut d := d0
    for i in [0:64] do
      let (f, g) :=
        if i < 16 then ((b &&& c) ||| (~~~b &&& d), i)
        else if i < 32 then ((d &&& b) ||| (~~~d &&& c), (5 * i + 1) % 16)
        else if i < 48 then (b ^^^ c ^^^ d, (3 * i + 5) % 16)
        else (c ^^^ (b ||| ~~~d), (7 * i) % 16)
      let f := f + a + kMd5[i]! + m[g]!
      a := d
      d := c
      c := b
      b := b + rotl32 f sMd5[i]!
    a0 := a0 + a
    b0 := b0 + b
    c0 := c0 + c
    d0 := d0 + d
  let mut out := ByteArray.empty
  for word in [a0, b0, c0, d0] do
    out := out.push word.toUInt8
    out := out.push (word >>> 8).toUInt8
    out := out.push (word >>> 16).toUInt8
    out := out.push (word >>> 24).toUInt8
  return out

/-- The `md5` password-auth response body: PostgreSQL's
`"md5" ++ hex(md5(hex(md5(password ++ user)) ++ salt))` (salt from
AuthenticationMD5Password). -/
def md5PasswordHash (user password : String) (salt : ByteArray) : String :=
  let inner := toHexLower (md5 (password.toUTF8 ++ user.toUTF8))
  "md5" ++ toHexLower (md5 (inner.toUTF8 ++ salt))

end Crypto
end Pg
