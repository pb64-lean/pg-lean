module

public section

namespace Pg
namespace Crypto
namespace Base64

/-!
Standard base64 (RFC 4648 §4) with mandatory padding — the alphabet SCRAM
uses for salts, proofs, and signatures. Decoding is strict: length must be a
multiple of 4, only canonical padding is accepted, no whitespace.
-/

private def alphabet : ByteArray :=
  "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/".toUTF8

def encode (bytes : ByteArray) : String := Id.run do
  let mut out := ByteArray.empty
  let full := bytes.size / 3
  for i in [0:full] do
    let o := 3 * i
    let n := (bytes.get! o).toNat <<< 16 ||| (bytes.get! (o + 1)).toNat <<< 8 |||
      (bytes.get! (o + 2)).toNat
    out := out.push (alphabet.get! (n >>> 18 &&& 63))
    out := out.push (alphabet.get! (n >>> 12 &&& 63))
    out := out.push (alphabet.get! (n >>> 6 &&& 63))
    out := out.push (alphabet.get! (n &&& 63))
  match bytes.size % 3 with
  | 1 =>
    let n := (bytes.get! (3 * full)).toNat <<< 16
    out := out.push (alphabet.get! (n >>> 18 &&& 63))
    out := out.push (alphabet.get! (n >>> 12 &&& 63))
    out := (out.push 61).push 61  -- "=="
  | 2 =>
    let n := (bytes.get! (3 * full)).toNat <<< 16 ||| (bytes.get! (3 * full + 1)).toNat <<< 8
    out := out.push (alphabet.get! (n >>> 18 &&& 63))
    out := out.push (alphabet.get! (n >>> 12 &&& 63))
    out := out.push (alphabet.get! (n >>> 6 &&& 63))
    out := out.push 61  -- '='
  | _ => pure ()
  String.fromUTF8! out

private def value? (c : UInt8) : Option Nat :=
  if c ≥ 65 && c ≤ 90 then some (c.toNat - 65)        -- 'A'..'Z'
  else if c ≥ 97 && c ≤ 122 then some (c.toNat - 71)  -- 'a'..'z'
  else if c ≥ 48 && c ≤ 57 then some (c.toNat + 4)    -- '0'..'9'
  else if c == 43 then some 62                        -- '+'
  else if c == 47 then some 63                        -- '/'
  else none

def decode? (s : String) : Option ByteArray := Id.run do
  let raw := s.toUTF8
  if raw.size % 4 != 0 then return none
  if raw.size == 0 then return some ByteArray.empty
  let pad : Nat :=
    if raw.get! (raw.size - 1) == 61 then
      if raw.get! (raw.size - 2) == 61 then 2 else 1
    else 0
  let mut out := ByteArray.empty
  for i in [0:raw.size / 4] do
    let o := 4 * i
    let lastGroup := o + 4 == raw.size
    let digits := if lastGroup then 4 - pad else 4
    let mut n := 0
    for j in [0:digits] do
      let some v := value? (raw.get! (o + j)) | return none
      n := n <<< 6 ||| v
    -- non-final '=' or digits after '=' are malformed
    for j in [digits:4] do
      if raw.get! (o + j) != 61 then return none
    match digits with
    | 4 =>
      out := out.push (UInt8.ofNat (n >>> 16 &&& 0xff))
      out := out.push (UInt8.ofNat (n >>> 8 &&& 0xff))
      out := out.push (UInt8.ofNat (n &&& 0xff))
    | 3 =>
      -- 18 bits carry 2 bytes; canonical iff the low 2 bits are zero
      if n &&& 0x3 != 0 then return none
      out := out.push (UInt8.ofNat (n >>> 10 &&& 0xff))
      out := out.push (UInt8.ofNat (n >>> 2 &&& 0xff))
    | 2 =>
      if n &&& 0xf != 0 then return none
      out := out.push (UInt8.ofNat (n >>> 4 &&& 0xff))
    | _ => return none
  return some out

end Base64
end Crypto
end Pg
