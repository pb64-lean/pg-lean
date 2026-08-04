module

public import Pg.Types.Digits

public section

namespace Pg

/-!
`numeric` — arbitrary-precision decimals in PostgreSQL's own representation:
base-10000 digits with a weight (position of the first digit relative to the
decimal point) and a display scale. Kept verbatim so no precision is ever
lost; convert to/from `String` for arithmetic elsewhere.

The text codec is written as explicit recursion over character lists rather
than as `for`/`while` loops over `String`: a `forIn` body and `String.splitOn`
are both opaque to the kernel, and `numeric` is the type where a silent
precision bug would be worst. `Pg.Types.Codec` proves
`PgNumeric.fromString_toString` on top of this shape.
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

/-! ### Rendering -/

/-- The base-10000 digit at group index `i` (`0` is the `weight` group). Out of
range it is `0`, which is exactly what the value's decimal expansion has
there. -/
@[expose] def digitAt (n : PgNumeric) (i : Int) : Nat :=
  if i < 0 then 0 else (n.digits[i.toNat]?.getD 0).toNat

/-- Whole base-10000 groups *after* the leading one in the integer part. A
negative weight renders the single group `0`, hence `Int.toNat`. -/
@[expose] def intGroups (n : PgNumeric) : Nat := n.weight.toNat

/-- Group index the rendering starts at: `0` when there is an integer part,
`weight` (negative) when the integer part is the lone `0` group — in both cases
`weight - intGroups`, so the rendered groups are always
`baseIndex … baseIndex + intGroups` followed by the fraction. -/
@[expose] def baseIndex (n : PgNumeric) : Int := n.weight - (n.intGroups : Int)

/-- The base-10000 groups a rendering covers: `k` of them, from group index
`start` outwards. Written as a list so the parser's regrouping can be matched
against it directly. -/
@[expose] def groupList (n : PgNumeric) (start : Int) : Nat → List Nat
  | 0 => []
  | k + 1 => n.digitAt start :: n.groupList (start + 1) k

/-- One base-10000 group as exactly four decimal characters. Equal to
`padDigits 4` on every in-range group (`< 10000`); out of range it keeps the
low four digits, which is what the fraction rendering always did. -/
@[expose] def digits4 (v : Nat) : List Char :=
  [digitChar (v / 1000), digitChar (v / 100), digitChar (v / 10), digitChar v]

/-- Integer-part characters: the leading group unpadded, every later group
zero-padded to four. -/
@[expose] def intChars (n : PgNumeric) : List Char :=
  natDigits (n.digitAt n.baseIndex) ++
    (n.groupList (n.baseIndex + 1) n.intGroups).flatMap (padDigits 4)

/-- Fraction characters: `k` decimal places, i.e. the first `k` characters of
the base-10000 groups just past the decimal point. -/
@[expose] def fracChars (n : PgNumeric) (k : Nat) : List Char :=
  ((n.groupList (n.weight + 1) ((k + 3) / 4)).flatMap digits4).take k

/-- The full decimal rendering of a finite `numeric`. -/
@[expose] def chars (n : PgNumeric) : List Char :=
  (if n.neg then ['-'] else []) ++ n.intChars ++
    (if n.dscale = 0 then [] else '.' :: n.fracChars n.dscale)

protected def toString (n : PgNumeric) : String :=
  match n.special with
  | some .nan => "NaN"
  | some .posInf => "Infinity"
  | some .negInf => "-Infinity"
  | none => String.ofList n.chars

instance : ToString PgNumeric := ⟨PgNumeric.toString⟩

/-- The rendering of a finite value, at the character level. -/
theorem toString_eq {n : PgNumeric} (h : n.special = none) :
    n.toString = String.ofList n.chars := by
  unfold PgNumeric.toString
  rw [h]

/-! ### Parsing -/

/-- The non-finite spellings PostgreSQL accepts. -/
@[expose] def specialOf : List Char → Option Special
  | ['N', 'a', 'N'] => some .nan
  | ['I', 'n', 'f', 'i', 'n', 'i', 't', 'y'] => some .posInf
  | ['+', 'I', 'n', 'f', 'i', 'n', 'i', 't', 'y'] => some .posInf
  | ['i', 'n', 'f'] => some .posInf
  | ['-', 'I', 'n', 'f', 'i', 'n', 'i', 't', 'y'] => some .negInf
  | ['-', 'i', 'n', 'f'] => some .negInf
  | _ => none

/-- Left-pad the integer digits to a multiple of four: that aligns the decimal
point with a base-10000 group boundary. -/
@[expose] def alignInt (ip : List Char) : List Char :=
  List.replicate ((4 - ip.length % 4) % 4) '0' ++ ip

/-- Right-pad the fraction digits to a multiple of four. -/
@[expose] def alignFrac (fp : List Char) : List Char :=
  fp ++ List.replicate ((4 - fp.length % 4) % 4) '0'

/-- Fold an aligned digit string into base-10000 digits, four characters at a
time. Structural recursion on the list; a `for` loop with a carry counter is
opaque to the kernel. A trailing partial group cannot occur (the input is
aligned) and is dropped, as the loop version did. -/
@[expose] def group4 : List Char → Array UInt16 → Array UInt16
  | a :: b :: c :: d :: rest, out =>
    group4 rest (out.push (UInt16.ofNat ((natOfDigits 0 [a, b, c, d]).getD 0)))
  | _, out => out

/-- Drop the zero groups the left-alignment introduced. -/
@[expose] def dropLeadZeros : List UInt16 → List UInt16
  | [] => []
  | d :: rest => if d == 0 then dropLeadZeros rest else d :: rest

/-- Drop the zero groups the right-alignment introduced. -/
@[expose] def dropTrailZeros (l : List UInt16) : List UInt16 :=
  (dropLeadZeros l.reverse).reverse

/-- Assemble the normalized value. Zero is canonical: no sign, no digits,
weight `0`, and only the display scale survives. -/
@[expose] def ofGroups (neg : Bool) (dscale : Nat) (lead : List UInt16) (w : Int) :
    PgNumeric :=
  match dropTrailZeros lead with
  | [] => { neg := false, digits := #[], weight := 0, dscale }
  | ds => { neg, digits := ds.toArray, weight := w, dscale }

/-- Group the aligned digit string, then strip the alignment's zero groups —
each leading one dropped lowers the weight by one. -/
@[expose] def ofDigitChars (neg : Bool) (ip fp : List Char) : PgNumeric :=
  ofGroups neg fp.length
    (dropLeadZeros (group4 (alignInt ip ++ alignFrac fp) #[]).toList)
    (((alignInt ip).length / 4 : Int) - 1 -
      (((group4 (alignInt ip ++ alignFrac fp) #[]).toList.length -
        (dropLeadZeros (group4 (alignInt ip ++ alignFrac fp) #[]).toList).length : Nat) : Int))

/-- Integer and fraction digits, after defaulting an absent integer part to
`0`. Rejects anything that is not a decimal digit. -/
@[expose] def ofParts (orig : String) (neg : Bool) (intPart fracPart : List Char) :
    Except String PgNumeric :=
  if (if intPart.isEmpty then ['0'] else intPart).all isAsciiDigit &&
      fracPart.all isAsciiDigit then
    .ok (ofDigitChars neg (if intPart.isEmpty then ['0'] else intPart) fracPart)
  else .error s!"numeric: cannot parse {orig}"

/-- Split the mantissa at the decimal point. More than one point is an error
(the loop version silently returned zero). -/
@[expose] def ofSigned (orig : String) (neg : Bool) (body : List Char) :
    Except String PgNumeric :=
  match body.splitOn '.' with
  | [i] => ofParts orig neg i []
  | [i, f] => ofParts orig neg i f
  | _ => .error s!"numeric: cannot parse {orig}"

/-- Strip an optional sign. Written with an `if` rather than a character
pattern so that proofs can rewrite it. -/
@[expose] def ofDecimalChars (orig : String) : List Char → Except String PgNumeric
  | [] => ofSigned orig false []
  | c :: rest =>
    if c == '-' then ofSigned orig true rest
    else if c == '+' then ofSigned orig false rest
    else ofSigned orig false (c :: rest)

@[expose] def ofChars (orig : String) (cs : List Char) : Except String PgNumeric :=
  match specialOf cs with
  | some sp => .ok { special := some sp }
  | none => ofDecimalChars orig cs

@[expose] def fromString (s : String) : Except String PgNumeric :=
  ofChars s (trimAsciiChars s.toList)

end PgNumeric

end Pg
