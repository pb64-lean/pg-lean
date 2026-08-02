module

public section

namespace Pg
namespace Crypto

/-!
SHA-256 (FIPS 180-4), pure Lean. Codegen-time cost is irrelevant here; at
runtime this is used for SCRAM-SHA-256 authentication (a few thousand
compressions per handshake via PBKDF2), well within pure-Lean performance.
-/

private def rotr32 (x : UInt32) (n : UInt32) : UInt32 :=
  (x >>> n) ||| (x <<< (32 - n))

private def k256 : Array UInt32 := #[
  0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
  0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
  0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
  0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
  0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
  0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
  0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
  0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2]

/-- Message padded to a whole number of 64-byte blocks: `0x80`, zeros, then the
original bit length as a big-endian 64-bit integer. -/
private def pad (msg : ByteArray) : ByteArray := Id.run do
  let bitLen : UInt64 := (UInt64.ofNat msg.size) * 8
  let mut data := msg.push 0x80
  let zeros := (64 + 56 - (msg.size + 1) % 64) % 64
  for _ in [0:zeros] do
    data := data.push 0
  for i in [0:8] do
    data := data.push (bitLen >>> (UInt64.ofNat ((7 - i) * 8))).toUInt8
  return data

def sha256 (msg : ByteArray) : ByteArray := Id.run do
  let data := pad msg
  let mut h0 : UInt32 := 0x6a09e667
  let mut h1 : UInt32 := 0xbb67ae85
  let mut h2 : UInt32 := 0x3c6ef372
  let mut h3 : UInt32 := 0xa54ff53a
  let mut h4 : UInt32 := 0x510e527f
  let mut h5 : UInt32 := 0x9b05688c
  let mut h6 : UInt32 := 0x1f83d9ab
  let mut h7 : UInt32 := 0x5be0cd19
  for blk in [0:data.size / 64] do
    let base := blk * 64
    let mut w : Array UInt32 := Array.empty
    for t in [0:16] do
      let o := base + t * 4
      w := w.push <|
        (data.get! o).toUInt32 <<< 24 |||
        (data.get! (o + 1)).toUInt32 <<< 16 |||
        (data.get! (o + 2)).toUInt32 <<< 8 |||
        (data.get! (o + 3)).toUInt32
    for t in [16:64] do
      let s0 := rotr32 w[t - 15]! 7 ^^^ rotr32 w[t - 15]! 18 ^^^ (w[t - 15]! >>> 3)
      let s1 := rotr32 w[t - 2]! 17 ^^^ rotr32 w[t - 2]! 19 ^^^ (w[t - 2]! >>> 10)
      w := w.push (w[t - 16]! + s0 + w[t - 7]! + s1)
    let mut a := h0
    let mut b := h1
    let mut c := h2
    let mut d := h3
    let mut e := h4
    let mut f := h5
    let mut g := h6
    let mut h := h7
    for t in [0:64] do
      let s1 := rotr32 e 6 ^^^ rotr32 e 11 ^^^ rotr32 e 25
      let ch := (e &&& f) ^^^ (~~~e &&& g)
      let temp1 := h + s1 + ch + k256[t]! + w[t]!
      let s0 := rotr32 a 2 ^^^ rotr32 a 13 ^^^ rotr32 a 22
      let maj := (a &&& b) ^^^ (a &&& c) ^^^ (b &&& c)
      let temp2 := s0 + maj
      h := g
      g := f
      f := e
      e := d + temp1
      d := c
      c := b
      b := a
      a := temp1 + temp2
    h0 := h0 + a
    h1 := h1 + b
    h2 := h2 + c
    h3 := h3 + d
    h4 := h4 + e
    h5 := h5 + f
    h6 := h6 + g
    h7 := h7 + h
  let mut out := ByteArray.empty
  for word in [h0, h1, h2, h3, h4, h5, h6, h7] do
    out := out.push (word >>> 24).toUInt8
    out := out.push (word >>> 16).toUInt8
    out := out.push (word >>> 8).toUInt8
    out := out.push word.toUInt8
  return out

end Crypto
end Pg
