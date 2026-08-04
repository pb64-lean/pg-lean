module

public import Std.Time
public import Pg.Protocol.Message
public import Pg.Crypto.Hex
public import Pg.Types.Oid
public import Pg.Types.Numeric
public import Pg.Types.Interval
import Std.Data.String.ToNat
import Std.Data.String.ToInt

public section

namespace Pg

open Std.Time

/-!
Wire codecs: `PgDecode`/`PgEncode` instances mapping PostgreSQL's text and
binary formats onto Lean types (`Std.Time` for temporal types, `PgNumeric`/
`PgInterval` for the lossless database representations).

Conventions: binary integers/floats are big-endian; temporal binary values
count from the PostgreSQL epoch 2000-01-01 (microseconds; dates in days);
`date`/`timestamp` infinity sentinels decode to errors (Std.Time has no
infinities — documented limitation).
-/

/-- Seconds from the Unix epoch (1970) to the PostgreSQL epoch (2000-01-01). -/
def pgEpochSeconds : Int := 946684800

/-- Every Std.Time Offset is a `UnitVal`; wrap an Int explicitly. -/
def uv {r} (x : Int) : Std.Time.Internal.UnitVal r := ⟨x⟩

def pgEpochDays : Int := 10957

class PgDecode (α : Type) where
  decodeText : UInt32 → String → Except String α
  decodeBinary : UInt32 → ByteArray → Except String α :=
    fun oid _ => throw s!"no binary decoder for oid {oid}"
  decodeNull : Except String α := throw "unexpected NULL"

class PgEncode (α : Type) where
  /-- Wire format produced (0 text, 1 binary). -/
  format : UInt16 := 0
  /-- Parameter type OID to declare in Parse (0 = let the server infer). -/
  typeOid : UInt32 := 0
  encode : α → Option ByteArray

/-- Decode one wire value given its column metadata. -/
def decodeValue [PgDecode α] (oid : UInt32) (format : UInt16) :
    Option ByteArray → Except String α
  | none => PgDecode.decodeNull
  | some bytes =>
    if format == 1 then
      PgDecode.decodeBinary oid bytes
    else
      match String.fromUTF8? bytes with
      | some s => PgDecode.decodeText oid s
      | none => throw "text value is not valid UTF-8"

/-- Encoded parameter with its format code, for `Connection.execute`-style
calls: `param (42 : Int)`. -/
def param (α : Type) [PgEncode α] (x : α) : UInt16 × Option ByteArray :=
  (PgEncode.format α, PgEncode.encode x)

instance [PgDecode α] : PgDecode (Option α) where
  decodeText oid s := some <$> PgDecode.decodeText oid s
  decodeBinary oid b := some <$> PgDecode.decodeBinary oid b
  decodeNull := pure none

instance [PgEncode α] : PgEncode (Option α) where
  format := PgEncode.format α
  typeOid := PgEncode.typeOid α
  encode
    | none => none
    | some x => PgEncode.encode x

-- ── binary readers ─────────────────────────────────────────────────────────

def rdInt16 (b : ByteArray) (off : Nat := 0) : Except String Int16 :=
  match Protocol.getUInt16? b off with
  | some v => pure v.toInt16
  | none => throw "truncated int16"

def rdInt32 (b : ByteArray) (off : Nat := 0) : Except String Int32 :=
  match Protocol.getUInt32? b off with
  | some v => pure v.toInt32
  | none => throw "truncated int32"

def rdUInt64 (b : ByteArray) (off : Nat := 0) : Except String UInt64 := do
  match Protocol.getUInt32? b off, Protocol.getUInt32? b (off + 4) with
  | some hi, some lo => pure (hi.toUInt64 <<< 32 ||| lo.toUInt64)
  | _, _ => throw "truncated int64"

def rdInt64 (b : ByteArray) (off : Nat := 0) : Except String Int64 :=
  (·.toInt64) <$> rdUInt64 b off

/-- Read a whole-width big-endian integer (2/4/8 bytes) as Int. -/
def rdIntAny (b : ByteArray) : Except String Int := do
  match b.size with
  | 2 => pure (← rdInt16 b).toInt
  | 4 => pure (← rdInt32 b).toInt
  | 8 => pure (← rdInt64 b).toInt
  | n => throw s!"unexpected integer width {n}"

def putInt64BE (v : Int64) : ByteArray := Id.run do
  let u := v.toUInt64
  let mut out := ByteArray.empty
  for i in [0:8] do
    out := out.push (u >>> (UInt64.ofNat ((7 - i) * 8))).toUInt8
  return out

-- ── numbers ────────────────────────────────────────────────────────────────

def intInRange (v : Int) (lo hi : Int) (what : String) : Except String Int := do
  unless lo ≤ v && v ≤ hi do throw s!"{what}: {v} out of range"
  pure v

instance : PgDecode Int where
  decodeText _ s :=
    match s.toInt? with
    | some v => pure v
    | none => throw s!"not an integer: {s}"
  decodeBinary _ b := rdIntAny b

instance : PgDecode Int64 where
  decodeText _ s := do
    let some v := s.toInt? | throw s!"not an integer: {s}"
    pure (Int64.ofInt (← intInRange v (-9223372036854775808) 9223372036854775807 "int8"))
  decodeBinary _ b := do pure (Int64.ofInt (← rdIntAny b))

instance : PgDecode Int32 where
  decodeText _ s := do
    let some v := s.toInt? | throw s!"not an integer: {s}"
    pure (Int32.ofInt (← intInRange v (-2147483648) 2147483647 "int4"))
  decodeBinary _ b := do
    pure (Int32.ofInt (← intInRange (← rdIntAny b) (-2147483648) 2147483647 "int4"))

instance : PgDecode Int16 where
  decodeText _ s := do
    let some v := s.toInt? | throw s!"not an integer: {s}"
    pure (Int16.ofInt (← intInRange v (-32768) 32767 "int2"))
  decodeBinary _ b := do
    pure (Int16.ofInt (← intInRange (← rdIntAny b) (-32768) 32767 "int2"))

instance : PgEncode Int where
  encode v := some (toString v).toUTF8

instance : PgEncode Int64 where
  typeOid := Oid.int8
  encode v := some (toString v).toUTF8

instance : PgEncode Int32 where
  typeOid := Oid.int4
  encode v := some (toString v).toUTF8

instance : PgEncode Int16 where
  typeOid := Oid.int2
  encode v := some (toString v).toUTF8

def floatNan : Float := Float.ofBits 0x7FF8000000000000
def floatInf : Float := Float.ofBits 0x7FF0000000000000

def parseFloat (s : String) : Except String Float := do
  match s with
  | "NaN" => return floatNan
  | "Infinity" | "inf" => return floatInf
  | "-Infinity" | "-inf" => return (-floatInf)
  | _ => pure ()
  let (neg, body) :=
    if s.startsWith "-" then (true, (s.toUTF8.extract 1 s.utf8ByteSize))
    else if s.startsWith "+" then (false, (s.toUTF8.extract 1 s.utf8ByteSize))
    else (false, s.toUTF8)
  let some body := String.fromUTF8? body | throw s!"not a float: {s}"
  let (mantissaPart, expPart) := match body.splitOn "e" with
    | [m] => (m, "0")
    | [m, e] => (m, e)
    | _ => ("", "")
  let (mantissaPart, expPart) := match mantissaPart.splitOn "E" with
    | [m] => (m, expPart)
    | [m, e] => (m, e)
    | _ => ("", "")
  let (intPart, fracPart) := match mantissaPart.splitOn "." with
    | [i] => (i, "")
    | [i, f] => (i, f)
    | _ => ("", "")
  let digits := intPart ++ fracPart
  unless !digits.isEmpty && digits.toList.all (fun c => '0' ≤ c && c ≤ '9') do
    throw s!"not a float: {s}"
  let some mantissa := digits.toNat? | throw s!"not a float: {s}"
  let some exp10 := expPart.toInt? | throw s!"not a float: {s}"
  let e := exp10 - Int.ofNat fracPart.length
  let f := if e < 0 then
    Float.ofScientific mantissa true e.natAbs
  else
    Float.ofScientific mantissa false e.toNat
  pure (if neg then -f else f)

instance : PgDecode Float where
  decodeText _ s := parseFloat s
  decodeBinary _ b := do
    match b.size with
    | 8 => pure (Float.ofBits (← rdUInt64 b))
    | 4 =>
      match Protocol.getUInt32? b 0 with
      | some v => pure (Float32.ofBits v).toFloat
      | none => throw "truncated float4"
    | n => throw s!"unexpected float width {n}"

instance : PgEncode Float where
  typeOid := Oid.float8
  encode v := some (toString v).toUTF8

instance : PgDecode Bool where
  decodeText _ s :=
    match s with
    | "t" | "true" => pure true
    | "f" | "false" => pure false
    | _ => throw s!"not a bool: {s}"
  decodeBinary _ b := do
    unless b.size == 1 do throw "bool must be 1 byte"
    pure (b.get! 0 != 0)

instance : PgEncode Bool where
  typeOid := Oid.bool
  encode v := some (if v then "t" else "f").toUTF8

-- ── strings and bytes ──────────────────────────────────────────────────────

instance : PgDecode String where
  decodeText _ s := pure s
  decodeBinary oid b := do
    if oid == Oid.uuid then
      unless b.size == 16 do throw "uuid must be 16 bytes"
      let hex := Crypto.toHexLower b
      let seg (lo hi : Nat) : String :=
        ((hex.toUTF8.extract lo hi) |> String.fromUTF8?).getD ""
      pure s!"{seg 0 8}-{seg 8 12}-{seg 12 16}-{seg 16 20}-{seg 20 32}"
    else if oid == Oid.jsonb then
      -- jsonb binary: 1-byte version prefix, then the JSON text
      unless b.size ≥ 1 && b.get! 0 == 1 do throw "unsupported jsonb version"
      match String.fromUTF8? (b.extract 1 b.size) with
      | some s => pure s
      | none => throw "jsonb payload is not UTF-8"
    else
      match String.fromUTF8? b with
      | some s => pure s
      | none => throw "binary value is not UTF-8 text"

instance : PgEncode String where
  encode v := some v.toUTF8

instance : PgDecode ByteArray where
  decodeText _ s := do
    unless s.startsWith "\\x" do throw "bytea text must be \\x-prefixed hex"
    let hexPart := (String.fromUTF8? (s.toUTF8.extract 2 s.utf8ByteSize)).getD ""
    match Crypto.ofHex? hexPart with
    | some bytes => pure bytes
    | none => throw "invalid bytea hex"
  decodeBinary _ b := pure b

instance : PgEncode ByteArray where
  format := 1
  typeOid := Oid.bytea
  encode v := some v

-- ── temporal types ─────────────────────────────────────────────────────────

def parseNatField (s : String) (what : String) : Except String Nat :=
  match s.toNat? with
  | some v => pure v
  | none => throw s!"bad {what}: {s}"

def rejectInfinity (s : String) : Except String Unit := do
  if s == "infinity" || s == "-infinity" then
    throw "date/timestamp infinity is not representable"

def parseDate (s : String) : Except String PlainDate := do
  rejectInfinity s
  match s.splitOn "-" with
  | [y, m, d] =>
    let y ← parseNatField y "year"
    let m ← parseNatField m "month"
    let d ← parseNatField d "day"
    let some mo := Std.Time.Internal.Bounded.LE.ofInt (Int.ofNat m)
      | throw s!"month out of range: {m}"
    let some da := Std.Time.Internal.Bounded.LE.ofInt (Int.ofNat d)
      | throw s!"day out of range: {d}"
    match PlainDate.ofYearMonthDay? (Int.ofNat y) mo da with
    | some date => pure date
    | none => throw s!"invalid date {s}"
  | _ => throw s!"cannot parse date {s} (BC dates unsupported)"

/-- `HH:MM:SS[.ffffff]` → nanoseconds since midnight. -/
def parseTimeNanos (s : String) : Except String Int := do
  let (hms, frac) := match s.splitOn "." with
    | [t] => (t, "")
    | [t, f] => (t, f)
    | _ => ("", "")
  match hms.splitOn ":" with
  | [h, m, sec] =>
    let h ← parseNatField h "hours"
    let m ← parseNatField m "minutes"
    let sec ← parseNatField sec "seconds"
    unless h < 24 && m < 60 && sec < 61 do throw s!"time out of range: {s}"
    let fracNanos ← do
      if frac.isEmpty then
        pure 0
      else
        let padded := (String.fromUTF8? ((frac ++ "000000000").toUTF8.extract 0 9)).getD ""
        pure (← parseNatField padded "fraction")
    pure (Int.ofNat (((h * 3600 + m * 60 + sec) * 1000000000) + fracNanos))
  | _ => throw s!"cannot parse time {s}"

def pad2 (v : Nat) : String :=
  if v < 10 then "0" ++ toString v else toString v

def pad4' (v : Int) : String :=
  let s := toString v.natAbs
  let padded := String.ofList (List.replicate (4 - min 4 s.length) '0') ++ s
  if v < 0 then "-" ++ padded else padded

def renderDate (d : PlainDate) : String :=
  s!"{pad4' d.year}-{pad2 d.month.toNat}-{pad2 d.day.toNat}"

def renderTimeNanos (nanos : Nat) : String :=
  let sec := nanos / 1000000000
  let sub := nanos % 1000000000
  let base := s!"{pad2 (sec / 3600)}:{pad2 (sec / 60 % 60)}:{pad2 (sec % 60)}"
  if sub == 0 then base
  else
    let micros := sub / 1000
    let f := toString (1000000 + micros)
    base ++ "." ++ ((f.toUTF8.extract 1 7 |> String.fromUTF8?).getD "")

instance : PgDecode PlainDate where
  decodeText _ s := parseDate s
  decodeBinary _ b := do
    let days := (← rdInt32 b).toInt
    if days == 2147483647 || days == -2147483648 then
      throw "date infinity is not representable"
    pure (PlainDate.ofDaysSinceUNIXEpoch (uv (days + pgEpochDays)))

instance : PgEncode PlainDate where
  typeOid := Oid.date
  encode d := some (renderDate d).toUTF8

instance : PgDecode PlainTime where
  decodeText _ s := do pure (PlainTime.ofNanoseconds (uv (← parseTimeNanos s)))
  decodeBinary _ b := do
    let micros := (← rdInt64 b).toInt
    pure (PlainTime.ofNanoseconds (uv (micros * 1000)))

instance : PgEncode PlainTime where
  typeOid := Oid.time
  encode t := some (renderTimeNanos t.toNanoseconds.toInt.toNat).toUTF8

def timestampSentinel (micros : Int) : Except String Unit := do
  if micros == 9223372036854775807 || micros == -9223372036854775808 then
    throw "timestamp infinity is not representable"

/-- Microseconds since 2000-01-01 → PlainDateTime (no zone). -/
def dateTimeOfPgMicros (micros : Int) : PlainDateTime :=
  PlainDateTime.ofTimestampAssumingUTC
    (Timestamp.ofNanosecondsSinceUnixEpoch (uv ((micros + pgEpochSeconds * 1000000) * 1000)))

instance : PgDecode PlainDateTime where
  decodeText _ s := do
    rejectInfinity s
    match s.splitOn " " with
    | [d, t] =>
      let date ← parseDate d
      let nanos ← parseTimeNanos t
      pure { date, time := PlainTime.ofNanoseconds (uv nanos) }
    | _ => throw s!"cannot parse timestamp {s}"
  decodeBinary _ b := do
    let micros := (← rdInt64 b).toInt
    timestampSentinel micros
    pure (dateTimeOfPgMicros micros)

instance : PgEncode PlainDateTime where
  typeOid := Oid.timestamp
  encode dt :=
    some s!"{renderDate dt.date} {renderTimeNanos dt.time.toNanoseconds.toInt.toNat}".toUTF8

/-- Timezone offset suffix of a timestamptz text value: `+HH`, `-HH:MM`, ... -/
def splitZoneSuffix (s : String) : Except String (String × Int) := do
  let raw := s.toUTF8
  let mut signPos : Option Nat := none
  for k in [0:raw.size] do
    let i := raw.size - 1 - k
    let b := raw.get! i
    if b == 43 || b == 45 then  -- '+' '-'
      signPos := some i
      break
    if b == 32 then break  -- reached the date/time separator space
  let some pos := signPos | throw s!"timestamptz without zone offset: {s}"
  let body := (String.fromUTF8? (raw.extract 0 pos)).getD ""
  let zone := (String.fromUTF8? (raw.extract pos raw.size)).getD ""
  let neg := zone.startsWith "-"
  let zoneBody := (String.fromUTF8? (zone.toUTF8.extract 1 zone.utf8ByteSize)).getD ""
  let (h, m) ← match zoneBody.splitOn ":" with
    | [h] => pure (← parseNatField h "zone hours", 0)
    | [h, m] => pure (← parseNatField h "zone hours", ← parseNatField m "zone minutes")
    | [h, m, _s] => pure (← parseNatField h "zone hours", ← parseNatField m "zone minutes")
    | _ => throw s!"bad zone offset {zone}"
  let secs := Int.ofNat (h * 3600 + m * 60)
  pure (body, if neg then -secs else secs)

instance : PgDecode Timestamp where
  decodeText _ s := do
    rejectInfinity s
    let (body, offsetSecs) ← splitZoneSuffix s
    match body.splitOn " " with
    | [d, t] =>
      let date ← parseDate d
      let nanos ← parseTimeNanos t
      let local' : PlainDateTime := { date, time := PlainTime.ofNanoseconds (uv nanos) }
      let localNanos := local'.toTimestampAssumingUTC.toNanosecondsSinceUnixEpoch.toInt
      pure (Timestamp.ofNanosecondsSinceUnixEpoch (uv (localNanos - offsetSecs * 1000000000)))
    | _ => throw s!"cannot parse timestamptz {s}"
  decodeBinary _ b := do
    let micros := (← rdInt64 b).toInt
    timestampSentinel micros
    pure (Timestamp.ofNanosecondsSinceUnixEpoch (uv ((micros + pgEpochSeconds * 1000000) * 1000)))

instance : PgEncode Timestamp where
  typeOid := Oid.timestamptz
  encode ts :=
    let dt := PlainDateTime.ofTimestampAssumingUTC ts
    some s!"{renderDate dt.date} {renderTimeNanos dt.time.toNanoseconds.toInt.toNat}+00".toUTF8

-- ── numeric and interval ───────────────────────────────────────────────────

instance : PgDecode PgNumeric where
  decodeText _ s := PgNumeric.fromString s
  decodeBinary _ b := do
    let ndigits := (← rdInt16 b 0).toInt.toNat
    let weight := (← rdInt16 b 2).toInt
    let sign := (← Protocol.getUInt16? b 4 |>.elim (throw "truncated numeric") pure)
    let dscale := (← rdInt16 b 6).toInt.toNat
    match sign.toNat with
    | 0xC000 => return { special := some .nan }
    | 0xD000 => return { special := some .posInf }
    | 0xF000 => return { special := some .negInf }
    | s' =>
      unless s' == 0 || s' == 0x4000 do throw s!"bad numeric sign {s'}"
      let mut digits : Array UInt16 := #[]
      for i in [0:ndigits] do
        match Protocol.getUInt16? b (8 + 2 * i) with
        | some d =>
          unless d < 10000 do throw s!"numeric digit {d} out of range"
          digits := digits.push d
        | none => throw "truncated numeric digits"
      pure { neg := s' == 0x4000, digits, weight, dscale }

def PgNumeric.toBinary (n : PgNumeric) : ByteArray := Id.run do
  let mut out := ByteArray.empty
  match n.special with
  | some sp =>
    out := Protocol.putUInt16 out 0
    out := Protocol.putUInt16 out 0
    out := Protocol.putUInt16 out (match sp with
      | .nan => 0xC000
      | .posInf => 0xD000
      | .negInf => 0xF000)
    out := Protocol.putUInt16 out 0
  | none =>
    out := Protocol.putUInt16 out (UInt16.ofNat n.digits.size)
    out := Protocol.putUInt16 out (Int16.ofInt n.weight).toUInt16
    out := Protocol.putUInt16 out (if n.neg then 0x4000 else 0)
    out := Protocol.putUInt16 out (UInt16.ofNat n.dscale)
    for d in n.digits do
      out := Protocol.putUInt16 out d
  return out

instance : PgEncode PgNumeric where
  typeOid := Oid.numeric
  encode n := some n.toString.toUTF8

instance : PgDecode PgInterval where
  decodeText _ s := PgInterval.fromString s
  decodeBinary _ b := do
    unless b.size == 16 do throw "interval must be 16 bytes"
    let micros := (← rdInt64 b 0).toInt
    let days := (← rdInt32 b 8).toInt
    let months := (← rdInt32 b 12).toInt
    pure { months, days, micros }

def PgInterval.toBinary (iv : PgInterval) : ByteArray :=
  putInt64BE (Int64.ofInt iv.micros) ++
    (Protocol.putUInt32 ByteArray.empty (Int32.ofInt iv.days).toUInt32) ++
    (Protocol.putUInt32 ByteArray.empty (Int32.ofInt iv.months).toUInt32)

instance : PgEncode PgInterval where
  typeOid := Oid.interval
  encode iv := some iv.toString.toUTF8

-- ── 1-D arrays ─────────────────────────────────────────────────────────────

/-- Parse `{a,"quo\"ted",NULL}` into raw element texts. 1-D only. -/
def parseArrayText (s : String) : Except String (Array (Option String)) := do
  let chars := s.trimAscii.toString.toList
  match chars with
  | '{' :: rest => do
    let mut elems : Array (Option String) := #[]
    let mut buf : List Char := []
    let mut quoted := false      -- current element was quoted
    let mut inQuotes := false
    let mut escaped := false
    let mut closed := false
    let mut sawAny := false
    for c in rest do
      if closed then throw s!"array: trailing characters in {s}"
      if escaped then
        buf := c :: buf
        escaped := false
      else if inQuotes then
        if c == '\\' then escaped := true
        else if c == '"' then inQuotes := false
        else buf := c :: buf
      else if c == '"' then
        inQuotes := true
        quoted := true
        sawAny := true
      else if c == ',' || c == '}' then
        let text := String.ofList buf.reverse
        if sawAny || !text.isEmpty then
          elems := elems.push (if !quoted && text == "NULL" then none else some text)
        else if c == ',' then
          throw s!"array: empty element in {s}"
        buf := []
        quoted := false
        sawAny := c == ','  -- after a comma another element must follow
        if c == '}' then closed := true
      else
        buf := c :: buf
        sawAny := true
    unless closed && !inQuotes && !escaped do throw s!"array: unterminated {s}"
    pure elems
  | _ => throw s!"not an array literal: {s}"

/-- One instance covers both nullable and strict element types: a NULL element
decodes through the element's `decodeNull` (so `Array (Option α)` yields
`none`, and `Array Int` reports the NULL as an error). -/
instance [PgDecode α] : PgDecode (Array α) where
  decodeText oid s := do
    let elems ← parseArrayText s
    let elemOid := Oid.arrayElem oid
    elems.mapM fun
      | none => PgDecode.decodeNull
      | some t => PgDecode.decodeText elemOid t
  decodeBinary oid b := do
    let ndim := (← rdInt32 b 0).toInt
    let elemOid := (← rdInt32 b 8).toUInt32
    let elemOid := if elemOid == 0 then Oid.arrayElem oid else elemOid
    if ndim == 0 then
      return #[]
    unless ndim == 1 do throw s!"only 1-D arrays supported (got {ndim}-D)"
    let count := (← rdInt32 b 12).toInt.toNat
    let mut off := 20
    let mut out : Array α := #[]
    for _ in [0:count] do
      let len := (← rdInt32 b off).toInt
      off := off + 4
      if len == -1 then
        out := out.push (← PgDecode.decodeNull)
      else
        let n := len.toNat
        unless off + n ≤ b.size do throw "truncated array element"
        out := out.push (← PgDecode.decodeBinary elemOid (b.extract off (off + n)))
        off := off + n
    pure out

-- ── roundtrip laws ─────────────────────────────────────────────────────────

/-!
Codec roundtrips: decoding what we encode yields the original value
(`decodeValue oid (format α) (encode x) = .ok x`). The reverse direction is
false in general (many wire spellings decode to one value), so these are the
strongest uniform laws the codecs admit. Covered: int2/int4/int8, unsized
Int, bool, bytea, text, uuid-as-text.
-/

/-- UTF-8 encode then decode is the identity (Strings are UTF-8-backed). -/
theorem fromUTF8?_toUTF8 (s : String) : String.fromUTF8? s.toUTF8 = some s := by
  simp only [String.fromUTF8?, String.toUTF8_eq_toByteArray]
  rw [dif_pos s.isValidUTF8]
  rfl

/-- In text format (`0`), `decodeValue` is exactly the instance's text
decoder on the encoded string. -/
theorem decodeValue_text (α : Type) [PgDecode α] (oid : UInt32) (s : String) :
    decodeValue (α := α) oid 0 (some s.toUTF8) = PgDecode.decodeText oid s := by
  rw [decodeValue]
  rw [if_neg (by decide)]
  rw [fromUTF8?_toUTF8]

theorem decode_encode_int2 (oid : UInt32) (x : Int16) :
    decodeValue (α := Int16) oid (PgEncode.format Int16) (PgEncode.encode x) = .ok x := by
  have htoInt : (toString x).toInt? = some x.toInt := by
    show (Int16.toInt x).repr.toInt? = _
    exact Int.toInt?_repr _
  have h1 := Int16.le_toInt x
  have h2 := Int16.toInt_le x
  have h3 : Int16.maxValue.toInt = 32767 := by decide
  show decodeValue oid 0 (some (toString x).toUTF8) = .ok x
  rw [decodeValue_text]
  simp only [PgDecode.decodeText, htoInt, intInRange]
  rw [if_pos (by
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨by omega, by omega⟩)]
  simp [Int16.ofInt_toInt]
  try rfl

theorem decode_encode_int4 (oid : UInt32) (x : Int32) :
    decodeValue (α := Int32) oid (PgEncode.format Int32) (PgEncode.encode x) = .ok x := by
  have htoInt : (toString x).toInt? = some x.toInt := by
    show (Int32.toInt x).repr.toInt? = _
    exact Int.toInt?_repr _
  have h1 := Int32.le_toInt x
  have h2 := Int32.toInt_le x
  have h3 : Int32.maxValue.toInt = 2147483647 := by decide
  show decodeValue oid 0 (some (toString x).toUTF8) = .ok x
  rw [decodeValue_text]
  simp only [PgDecode.decodeText, htoInt, intInRange]
  rw [if_pos (by
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨by omega, by omega⟩)]
  simp [Int32.ofInt_toInt]
  try rfl

theorem decode_encode_int8 (oid : UInt32) (x : Int64) :
    decodeValue (α := Int64) oid (PgEncode.format Int64) (PgEncode.encode x) = .ok x := by
  have htoInt : (toString x).toInt? = some x.toInt := by
    show (Int64.toInt x).repr.toInt? = _
    exact Int.toInt?_repr _
  have h1 := Int64.le_toInt x
  have h2 := Int64.toInt_le x
  have h3 : Int64.maxValue.toInt = 9223372036854775807 := by decide
  show decodeValue oid 0 (some (toString x).toUTF8) = .ok x
  rw [decodeValue_text]
  simp only [PgDecode.decodeText, htoInt, intInRange]
  rw [if_pos (by
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨by omega, by omega⟩)]
  simp [Int64.ofInt_toInt]
  try rfl

/-- Unsized `Int` (server-inferred parameter type): no range check at all. -/
theorem decode_encode_int (oid : UInt32) (x : Int) :
    decodeValue (α := Int) oid (PgEncode.format Int) (PgEncode.encode x) = .ok x := by
  show decodeValue oid 0 (some (toString x).toUTF8) = .ok x
  rw [decodeValue_text]
  simp [PgDecode.decodeText]
  try rfl

theorem decode_encode_bool (oid : UInt32) (x : Bool) :
    decodeValue (α := Bool) oid (PgEncode.format Bool) (PgEncode.encode x) = .ok x := by
  show decodeValue oid 0 (some (if x then "t" else "f").toUTF8) = .ok x
  cases x <;> rw [decodeValue_text] <;> rfl

theorem decode_encode_text (oid : UInt32) (s : String) :
    decodeValue (α := String) oid (PgEncode.format String) (PgEncode.encode s) = .ok s := by
  show decodeValue oid 0 (some s.toUTF8) = .ok s
  rw [decodeValue_text]
  rfl

/-- uuid values travel as text; the binary 16-byte decoder has no encoder
counterpart, so text is the roundtrip that exists. -/
theorem decode_encode_uuid (s : String) :
    decodeValue (α := String) Oid.uuid (PgEncode.format String) (PgEncode.encode s) =
      .ok s :=
  decode_encode_text Oid.uuid s

theorem decode_encode_bytea (oid : UInt32) (b : ByteArray) :
    decodeValue (α := ByteArray) oid (PgEncode.format ByteArray) (PgEncode.encode b) =
      .ok b := by
  show decodeValue oid 1 (some b) = .ok b
  rw [decodeValue]
  rw [if_pos (by decide)]
  rfl

end Pg
