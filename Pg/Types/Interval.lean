module

public import Pg.Types.Digits

public section

namespace Pg

/-!
`interval` — PostgreSQL's three-component duration: months, days, and
microseconds are NOT interconvertible (a month is not a fixed number of days,
a day not a fixed number of hours under DST), so the wire triple is preserved
as-is. Text form follows the default `postgres` interval style.

Both directions are explicit recursion over character lists: a `for` loop with
mutable state and `String.splitOn` are opaque to the kernel, and
`Pg.Types.Codec` proves `PgInterval.fromString_toString` on top of this shape.
-/

structure PgInterval where
  months : Int := 0
  days : Int := 0
  micros : Int := 0
  deriving Repr, BEq, Inhabited

namespace PgInterval

/-! ### Rendering -/

/-- Decimal characters of an `Int`, sign included. -/
@[expose] def intChars (v : Int) : List Char :=
  if v < 0 then '-' :: natDigits v.natAbs else natDigits v.natAbs

/-- `[-]HH:MM:SS`, each field at least two digits, plus `.ffffff` when there is
a microsecond remainder. Hours are not capped: an interval is a duration, not a
time of day. -/
@[expose] def timeChars (micros : Int) : List Char :=
  (if micros < 0 then ['-'] else []) ++
    padDigits 2 (micros.natAbs / 3600000000) ++
    ':' :: padDigits 2 (micros.natAbs / 60000000 % 60) ++
    ':' :: padDigits 2 (micros.natAbs / 1000000 % 60) ++
    (if micros.natAbs % 1000000 = 0 then []
      else '.' :: padDigits 6 (micros.natAbs % 1000000))

/-- The space-separated tokens of the rendering. A zero component is omitted,
except that an all-zero interval still renders its time piece. -/
@[expose] def tokens (iv : PgInterval) : List (List Char) :=
  (if iv.months = 0 then [] else [intChars iv.months, ['m', 'o', 'n', 's']]) ++
  (if iv.days = 0 then [] else [intChars iv.days, ['d', 'a', 'y', 's']]) ++
  (if iv.micros = 0 ∧ ¬(iv.months = 0 ∧ iv.days = 0) then [] else [timeChars iv.micros])

/-- Join with single spaces (`String.intercalate " "`, at the character
level). -/
@[expose] def joinSpace : List (List Char) → List Char
  | [] => []
  | [p] => p
  | p :: rest => p ++ ' ' :: joinSpace rest

@[expose] def chars (iv : PgInterval) : List Char := joinSpace iv.tokens

protected def toString (iv : PgInterval) : String := String.ofList iv.chars

instance : ToString PgInterval := ⟨PgInterval.toString⟩

/-! ### Parsing -/

/-- Optional sign, then a decimal field. Matches `String.toInt?`. -/
@[expose] def intOfChars : List Char → Option Int
  | '-' :: rest => (natOfDigitsFull rest).map (fun n => -Int.ofNat n)
  | cs => (natOfDigitsFull cs).map Int.ofNat

/-- `HH:MM:SS` plus an already-parsed microsecond remainder. -/
@[expose] def hmsMicros (orig : String) (hms : List Char) (frac : Nat) :
    Except String Int :=
  match hms.splitOn ':' with
  | [h, m, s] =>
    match natOfDigitsFull h, natOfDigitsFull m, natOfDigitsFull s with
    | some h, some m, some s => .ok (Int.ofNat ((h * 3600 + m * 60 + s) * 1000000 + frac))
    | _, _, _ => .error s!"interval: bad time {orig}"
  | _ => .error s!"interval: cannot parse time {orig}"

/-- A fraction of a second: right-pad with zeros and keep six places, so `.5`
is 500000 microseconds. -/
@[expose] def fracMicros (frac : List Char) : Option Nat :=
  natOfDigitsFull ((frac ++ List.replicate 6 '0').take 6)

@[expose] def timeMagnitude (orig : String) (body : List Char) : Except String Int :=
  match body.splitOn '.' with
  | [hms] => hmsMicros orig hms 0
  | [hms, frac] =>
    match fracMicros frac with
    | some v => hmsMicros orig hms v
    | none => .error s!"interval: bad fraction {orig}"
  | _ => .error s!"interval: cannot parse time {orig}"

@[expose] def parseTime (orig : String) : List Char → Except String Int
  | '-' :: rest => (timeMagnitude orig rest).map (fun v => -v)
  | '+' :: rest => timeMagnitude orig rest
  | body => timeMagnitude orig body

/-- One token at a time, carrying the accumulated interval and a number
awaiting its unit word. Explicit recursion — the `for` loop this replaces had
two mutable variables and was opaque to the kernel. -/
@[expose] def step (orig : String) (iv : PgInterval) (pending : Option Int) :
    List (List Char) → Except String PgInterval
  | [] => if pending.isNone then .ok iv else .error "interval: trailing number"
  | tok :: rest =>
    if tok.contains ':' then
      if pending.isNone then
        match parseTime (String.ofList tok) tok with
        | .ok us => step orig { iv with micros := iv.micros + us } none rest
        | .error e => .error e
      else .error s!"interval: dangling number before {String.ofList tok}"
    else
      match pending with
      | none =>
        match intOfChars tok with
        | some n => step orig iv (some n) rest
        | none => .error s!"interval: expected number, got {String.ofList tok}"
      | some n =>
        if ['y', 'e', 'a', 'r'].isPrefixOf tok then
          step orig { iv with months := iv.months + n * 12 } none rest
        else if ['m', 'o', 'n'].isPrefixOf tok then
          step orig { iv with months := iv.months + n } none rest
        else if ['w', 'e', 'e', 'k'].isPrefixOf tok then
          step orig { iv with days := iv.days + n * 7 } none rest
        else if ['d', 'a', 'y'].isPrefixOf tok then
          step orig { iv with days := iv.days + n } none rest
        else .error s!"interval: unknown unit {String.ofList tok}"

/-- Parses the default `postgres` output style, e.g.
`"1 year 2 mons 3 days 04:05:06.789"`, `"-00:00:01.5"`, `"00:00:00"`. -/
def fromString (s : String) : Except String PgInterval :=
  step s {} none (((trimAsciiChars s.toList).splitOn ' ').filter (fun t => !t.isEmpty))

end PgInterval

end Pg
