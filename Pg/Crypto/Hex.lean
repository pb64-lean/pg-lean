module

public section

namespace Pg
namespace Crypto

/-!
Lowercase hex encoding/decoding for byte arrays. Needed by MD5 password
hashing (PostgreSQL transmits `"md5" ++ hex(...)`) and by test vectors.
-/

private def hexDigits : ByteArray := "0123456789abcdef".toUTF8

def toHexLower (bytes : ByteArray) : String := Id.run do
  let mut out := ByteArray.empty
  for i in [0:bytes.size] do
    let b := bytes.get! i
    out := out.push (hexDigits.get! (b >>> 4).toNat)
    out := out.push (hexDigits.get! (b &&& 0xf).toNat)
  String.fromUTF8! out

private def hexVal? (c : UInt8) : Option UInt8 :=
  if c ≥ 48 && c ≤ 57 then some (c - 48)        -- '0'..'9'
  else if c ≥ 97 && c ≤ 102 then some (c - 87)  -- 'a'..'f'
  else if c ≥ 65 && c ≤ 70 then some (c - 55)   -- 'A'..'F'
  else none

/-- Core has no `Repr ByteArray`; print as hex so byte values in test and
error output are readable. -/
instance : Repr ByteArray where
  reprPrec bytes _ := .text s!"bytes\"{toHexLower bytes}\""

/-- Strict hex decode: even length, hex digits only (either case). -/
def ofHex? (s : String) : Option ByteArray := Id.run do
  let raw := s.toUTF8
  if raw.size % 2 != 0 then return none
  let mut out := ByteArray.empty
  for i in [0:raw.size / 2] do
    let some hi := hexVal? (raw.get! (2 * i)) | return none
    let some lo := hexVal? (raw.get! (2 * i + 1)) | return none
    out := out.push (hi <<< 4 ||| lo)
  return some out

end Crypto
end Pg
