module

public section

namespace Pg

/-!
`numeric` — arbitrary-precision decimals in PostgreSQL's own representation:
base-10000 digits with a weight (position of the first digit relative to the
decimal point) and a display scale. Kept verbatim so no precision is ever
lost; convert to/from `String` for arithmetic elsewhere.
-/

inductive PgNumeric.Special where
  | nan
  | posInf
  | negInf
  deriving Repr, BEq, Inhabited

structure PgNumeric where
  neg : Bool := false
  /-- Base-10000 digits, most significant first; empty means 0. -/
  digits : Array UInt16 := #[]
  /-- Value = Σ digits[i] × 10000^(weight − i). -/
  weight : Int := 0
  /-- Decimal digits displayed after the point. -/
  dscale : Nat := 0
  special : Option PgNumeric.Special := none
  deriving Repr, BEq, Inhabited

namespace PgNumeric

private def digitAt (n : PgNumeric) (i : Int) : Nat :=
  if i < 0 then 0
  else (n.digits[i.toNat]?.getD 0).toNat

private def pad4 (v : Nat) : String :=
  let s := toString v
  String.ofList (List.replicate (4 - min 4 s.length) '0') ++ s

protected def toString (n : PgNumeric) : String :=
  match n.special with
  | some .nan => "NaN"
  | some .posInf => "Infinity"
  | some .negInf => "-Infinity"
  | none => Id.run do
    let mut intPart := ""
    if n.weight < 0 then
      intPart := "0"
    else
      for k in [0:(n.weight.toNat + 1)] do
        let v := n.digitAt (Int.ofNat k)
        intPart := intPart ++ (if k == 0 then toString v else pad4 v)
    let mut fracPart := ""
    if n.dscale > 0 then
      for k in [0:n.dscale] do
        let gi := n.weight + 1 + Int.ofNat (k / 4)
        let v := n.digitAt gi
        let d := (v / Nat.pow 10 (3 - k % 4)) % 10
        fracPart := fracPart ++ toString d
    let sign := if n.neg then "-" else ""
    return sign ++ intPart ++ (if n.dscale > 0 then "." ++ fracPart else "")

instance : ToString PgNumeric := ⟨PgNumeric.toString⟩

private def isDigits (s : String) : Bool :=
  !s.isEmpty && s.toList.all (fun c => '0' ≤ c && c ≤ '9')

private def digitVal (c : Char) : Nat := c.toNat - 48

/-- Group decimal digit chars into base-10000 digits, aligning the decimal
point at a group boundary: the integer part is padded on the LEFT to a
multiple of 4, the fraction on the RIGHT. -/
private def group4 (intDigits fracDigits : List Char) : Array UInt16 × Int := Id.run do
  let intPad := (4 - intDigits.length % 4) % 4
  let padded := List.replicate intPad '0' ++ intDigits
  let fracPad := (4 - fracDigits.length % 4) % 4
  let paddedFrac := fracDigits ++ List.replicate fracPad '0'
  let all := padded ++ paddedFrac
  let mut digits : Array UInt16 := #[]
  let mut acc := 0
  let mut cnt := 0
  for c in all do
    acc := acc * 10 + digitVal c
    cnt := cnt + 1
    if cnt == 4 then
      digits := digits.push (UInt16.ofNat acc)
      acc := 0
      cnt := 0
  let weight : Int := Int.ofNat (padded.length / 4) - 1
  return (digits, weight)

def fromString (s : String) : Except String PgNumeric := do
  let s := s.trimAscii.toString
  match s with
  | "NaN" => return { special := some .nan }
  | "Infinity" | "+Infinity" | "inf" => return { special := some .posInf }
  | "-Infinity" | "-inf" => return { special := some .negInf }
  | _ => pure ()
  let (neg, rest) :=
    if s.startsWith "-" then (true, (s.toUTF8.extract 1 s.utf8ByteSize))
    else if s.startsWith "+" then (false, (s.toUTF8.extract 1 s.utf8ByteSize))
    else (false, s.toUTF8)
  let some rest := String.fromUTF8? rest | throw "numeric: bad input"
  let (intPart, fracPart) := match rest.splitOn "." with
    | [i] => (i, "")
    | [i, f] => (i, f)
    | _ => ("", "")
  let intPart := if intPart.isEmpty then "0" else intPart
  unless isDigits intPart && (fracPart.isEmpty || isDigits fracPart) do
    throw s!"numeric: cannot parse {s}"
  let (digits, weight) := group4 intPart.toList fracPart.toList
  -- normalize: strip leading and trailing zero groups
  let mut digits := digits
  let mut weight := weight
  while digits.size > 0 && digits[0]! == 0 do
    digits := digits.extract 1 digits.size
    weight := weight - 1
  while digits.size > 0 && digits[digits.size - 1]! == 0 do
    digits := digits.extract 0 (digits.size - 1)
  if digits.isEmpty then
    return { neg := false, digits := #[], weight := 0, dscale := fracPart.length }
  return { neg, digits, weight, dscale := fracPart.length }

end PgNumeric

end Pg
