module

public section

namespace Pg
namespace TestSupport

/-!
Byte-fixture helpers for wire tests. `hex` tolerates whitespace and `|`
separators so golden literals can be grouped readably:
`hex "52 | 00 00 00 08 | 00 00 00 00"`. Bad input panics — these are
compile-time-authored test constants, not data.
-/

private def hexVal? (c : Char) : Option UInt8 :=
  if '0' ≤ c && c ≤ '9' then some (UInt8.ofNat (c.toNat - 48))
  else if 'a' ≤ c && c ≤ 'f' then some (UInt8.ofNat (c.toNat - 87))
  else if 'A' ≤ c && c ≤ 'F' then some (UInt8.ofNat (c.toNat - 55))
  else none

def hex (s : String) : ByteArray := Id.run do
  let mut out := ByteArray.empty
  let mut pending : Option UInt8 := none
  for c in s.toList do
    if c == ' ' || c == '\n' || c == '\t' || c == '|' then
      continue
    match hexVal? c with
    | none => panic! s!"hex: bad character {c} in {s}"
    | some v =>
      match pending with
      | none => pending := some v
      | some hi =>
        out := out.push (hi <<< 4 ||| v)
        pending := none
  if pending.isSome then panic! s!"hex: odd digit count in {s}"
  return out

def ascii (s : String) : ByteArray := s.toUTF8

def hexDump (bytes : ByteArray) : String := Id.run do
  let digits := "0123456789abcdef".toUTF8
  let mut out := ByteArray.empty
  for i in [0:bytes.size] do
    if i > 0 then out := out.push 32
    let b := bytes.get! i
    out := out.push (digits.get! (b >>> 4).toNat)
    out := out.push (digits.get! (b &&& 0xf).toNat)
  String.fromUTF8! out

end TestSupport
end Pg
