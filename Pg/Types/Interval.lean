module

public section

namespace Pg

/-!
`interval` — PostgreSQL's three-component duration: months, days, and
microseconds are NOT interconvertible (a month is not a fixed number of days,
a day not a fixed number of hours under DST), so the wire triple is preserved
as-is. Text form follows the default `postgres` interval style.
-/

structure PgInterval where
  months : Int := 0
  days : Int := 0
  micros : Int := 0
  deriving Repr, BEq, Inhabited

namespace PgInterval

private def pad2 (v : Nat) : String :=
  if v < 10 then "0" ++ toString v else toString v

protected def toString (iv : PgInterval) : String := Id.run do
  let mut pieces : Array String := #[]
  if iv.months != 0 then
    pieces := pieces.push s!"{iv.months} mons"
  if iv.days != 0 then
    pieces := pieces.push s!"{iv.days} days"
  let neg := iv.micros < 0
  let us := iv.micros.natAbs
  let h := us / 3600000000
  let m := us / 60000000 % 60
  let s := us / 1000000 % 60
  let frac := us % 1000000
  let mut time := (if neg then "-" else "") ++ s!"{pad2 h}:{pad2 m}:{pad2 s}"
  if frac != 0 then
    let f := toString (1000000 + frac)  -- "1ffffff": drop the lead, keep zeros
    time := time ++ "." ++ (f.toUTF8.extract 1 7 |> String.fromUTF8?).getD ""
  if iv.micros != 0 || pieces.isEmpty then
    pieces := pieces.push time
  return String.intercalate " " pieces.toList

instance : ToString PgInterval := ⟨PgInterval.toString⟩

private def parseTime (tok : String) : Except String Int := do
  let (neg, body) :=
    if tok.startsWith "-" then (true, (tok.toUTF8.extract 1 tok.utf8ByteSize))
    else if tok.startsWith "+" then (false, (tok.toUTF8.extract 1 tok.utf8ByteSize))
    else (false, tok.toUTF8)
  let some body := String.fromUTF8? body | throw "interval: bad time"
  let (hms, frac) := match body.splitOn "." with
    | [t] => (t, "")
    | [t, f] => (t, f)
    | _ => ("", "")
  let micros ← match hms.splitOn ":" with
    | [h, m, s] =>
      let some h := h.toNat? | throw s!"interval: bad hours {hms}"
      let some m := m.toNat? | throw s!"interval: bad minutes {hms}"
      let some s := s.toNat? | throw s!"interval: bad seconds {hms}"
      pure (Int.ofNat ((h * 3600 + m * 60 + s) * 1000000))
    | _ => throw s!"interval: cannot parse time {tok}"
  let fracUs ← do
    if frac.isEmpty then
      pure 0
    else
      let padded := (frac ++ "000000").toUTF8.extract 0 6
      let some fs := String.fromUTF8? padded | throw "interval: bad fraction"
      let some v := fs.toNat? | throw s!"interval: bad fraction {frac}"
      pure (Int.ofNat v)
  let total := micros + fracUs
  pure (if neg then -total else total)

/-- Parses the default `postgres` output style, e.g.
`"1 year 2 mons 3 days 04:05:06.789"`, `"-00:00:01.5"`, `"00:00:00"`. -/
def fromString (s : String) : Except String PgInterval := do
  let tokens := (s.trimAscii.toString.splitOn " ").filter (!·.isEmpty)
  let mut iv : PgInterval := {}
  let mut pendingNum : Option Int := none
  for tok in tokens do
    if tok.toList.contains ':' then
      unless pendingNum.isNone do throw s!"interval: dangling number before {tok}"
      iv := { iv with micros := iv.micros + (← parseTime tok) }
    else
      match pendingNum with
      | none =>
        let some n := tok.toInt? | throw s!"interval: expected number, got {tok}"
        pendingNum := some n
      | some n =>
        pendingNum := none
        if tok.startsWith "year" then
          iv := { iv with months := iv.months + n * 12 }
        else if tok.startsWith "mon" then
          iv := { iv with months := iv.months + n }
        else if tok.startsWith "week" then
          iv := { iv with days := iv.days + n * 7 }
        else if tok.startsWith "day" then
          iv := { iv with days := iv.days + n }
        else
          throw s!"interval: unknown unit {tok}"
  unless pendingNum.isNone do throw "interval: trailing number"
  pure iv

end PgInterval

end Pg
