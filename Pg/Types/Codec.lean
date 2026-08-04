module

public import Std.Time
public import Pg.Protocol.Message
public import Pg.Crypto.Hex
public import Pg.Types.Digits
public import Pg.Types.Oid
public import Pg.Types.Numeric
public import Pg.Types.Interval
import all Std.Time.Date.PlainDate
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

def putInt64BE (v : Int64) : ByteArray :=
  Protocol.putUInt32 (Protocol.putUInt32 ByteArray.empty (v.toUInt64 >>> 32).toUInt32)
    v.toUInt64.toUInt32

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

/-- No `parseFloat (toString v) = v` law is stated, and that is deliberate:
IEEE-754 text roundtripping is not unconditionally true (`toString` prints a
shortest decimal and `parseFloat` re-rounds it, so the claim needs
`Float.ofScientific`'s rounding to be proved a left inverse of shortest-form
printing). That is a real-arithmetic development this repository does not have
— core + Std only, no Mathlib. The live matrix covers `float4`/`float8` by
example instead. -/
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

def rejectInfinity (s : String) : Except String Unit := do
  if s == "infinity" || s == "-infinity" then
    throw "date/timestamp infinity is not representable"

/-- The three decimal fields of a `YYYY-MM-DD` date, before any calendar
validation. -/
def dateFields (s : String) : Except String (Nat × Nat × Nat) :=
  match splitOnChar '-' s with
  | [y, m, d] =>
    match parseNatField y "year", parseNatField m "month", parseNatField d "day" with
    | .ok y, .ok m, .ok d => .ok (y, m, d)
    | .error e, _, _ => .error e
    | _, .error e, _ => .error e
    | _, _, .error e => .error e
  | _ => throw s!"cannot parse date {s} (BC dates unsupported)"

/-- `infinity` and `-infinity` fail `dateFields` anyway; reporting them
separately only replaces the message, so the check sits on the error path. -/
def parseDate (s : String) : Except String PlainDate :=
  match dateFields s with
  | .error e =>
    match rejectInfinity s with
    | .error e' => .error e'
    | .ok _ => .error e
  | .ok (y, m, d) =>
    match Std.Time.Internal.Bounded.LE.ofInt (Int.ofNat m),
        Std.Time.Internal.Bounded.LE.ofInt (Int.ofNat d) with
    | some mo, some da =>
      match PlainDate.ofYearMonthDay? (Int.ofNat y) mo da with
      | some date => .ok date
      | none => .error s!"invalid date {s}"
    | none, _ => .error s!"month out of range: {m}"
    | _, none => .error s!"day out of range: {d}"

/-- Fractional seconds text → nanoseconds: right-pad to 9 digits and read. -/
def fracNanos (frac : String) : Except String Nat :=
  if frac.isEmpty then .ok 0
  else parseNatField
    (String.ofList (List.take 9 (frac.toList ++ List.replicate 9 '0'))) "fraction"

/-- `HH:MM:SS` plus an already-split fractional part → nanoseconds. -/
def hmsNanos (hms frac : String) : Except String Int :=
  match splitOnChar ':' hms with
  | [hs, ms, ss] =>
    match parseNatField hs "hours", parseNatField ms "minutes",
        parseNatField ss "seconds", fracNanos frac with
    | .ok h, .ok m, .ok sec, .ok nanos =>
      if h < 24 && m < 60 && sec < 61 then
        .ok (Int.ofNat (((h * 3600 + m * 60 + sec) * 1000000000) + nanos))
      else .error s!"time out of range: {hms}"
    | .error e, _, _, _ => .error e
    | _, .error e, _, _ => .error e
    | _, _, .error e, _ => .error e
    | _, _, _, .error e => .error e
  | _ => throw s!"cannot parse time {hms}"

/-- `HH:MM:SS[.ffffff]` → nanoseconds since midnight. -/
def parseTimeNanos (s : String) : Except String Int :=
  match splitOnChar '.' s with
  | [hms] => hmsNanos hms ""
  | [hms, frac] => hmsNanos hms frac
  | _ => throw s!"cannot parse time {s}"

def pad2 (v : Nat) : String := String.ofList (padDigits 2 v)

/-- Zero-padded 4-digit year with an explicit sign for BC dates. -/
def yearChars (v : Int) : List Char :=
  if v < 0 then '-' :: padDigits 4 v.natAbs else padDigits 4 v.natAbs

def pad4' (v : Int) : String := String.ofList (yearChars v)

def dateChars (d : PlainDate) : List Char :=
  yearChars d.year ++
    '-' :: (padDigits 2 d.month.toNat ++ '-' :: padDigits 2 d.day.toNat)

def renderDate (d : PlainDate) : String := String.ofList (dateChars d)

def timeChars (nanos : Nat) : List Char :=
  padDigits 2 (nanos / 1000000000 / 3600) ++
    ':' :: (padDigits 2 (nanos / 1000000000 / 60 % 60) ++
      ':' :: (padDigits 2 (nanos / 1000000000 % 60) ++
        (if nanos % 1000000000 == 0 then []
         else '.' :: padDigits 6 (nanos % 1000000000 / 1000))))

def renderTimeNanos (nanos : Nat) : String := String.ofList (timeChars nanos)

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

/-- The calendar date and the nanoseconds-since-midnight of a `YYYY-MM-DD
HH:MM:SS[.ffffff]` timestamp. Both halves are pg-lean's own text codecs;
turning the nanoseconds into a `PlainTime` is `Std.Time`'s job. -/
def timestampFields (s : String) : Except String (PlainDate × Int) :=
  match splitOnChar ' ' s with
  | [d, t] =>
    match parseDate d, parseTimeNanos t with
    | .ok date, .ok nanos => .ok (date, nanos)
    | .error e, _ => .error e
    | _, .error e => .error e
  | _ => .error s!"cannot parse timestamp {s}"

instance : PgDecode PlainDateTime where
  decodeText _ s :=
    match timestampFields s with
    | .error e =>
      match rejectInfinity s with
      | .error e' => .error e'
      | .ok _ => .error e
    | .ok (date, nanos) => .ok { date, time := PlainTime.ofNanoseconds (uv nanos) }
  decodeBinary _ b := do
    let micros := (← rdInt64 b).toInt
    timestampSentinel micros
    pure (dateTimeOfPgMicros micros)

/-- `YYYY-MM-DD HH:MM:SS[.ffffff]` — the date and time-of-day renderings
joined by the separator space. -/
def renderTimestamp (d : PlainDate) (nanos : Nat) : String :=
  String.ofList (dateChars d ++ ' ' :: timeChars nanos)

instance : PgEncode PlainDateTime where
  typeOid := Oid.timestamp
  encode dt := some (renderTimestamp dt.date dt.time.toNanoseconds.toInt.toNat).toUTF8

/-- Length of the trailing zone offset, scanning the reversed text: stop at the
first `+`/`-` (that is the sign) or at the date/time separator space. -/
def zoneSuffixLen : List Char → Option Nat
  | [] => none
  | c :: rest =>
    if c == '+' || c == '-' then some 1
    else if c == ' ' then none
    else (zoneSuffixLen rest).map (· + 1)

/-- Timezone offset suffix of a timestamptz text value: `+HH`, `-HH:MM`, ... -/
def splitZoneSuffix (s : String) : Except String (String × Int) :=
  match zoneSuffixLen s.toList.reverse with
  | none => throw s!"timestamptz without zone offset: {s}"
  | some k =>
    let pos := s.toList.length - k
    let body := String.ofList (s.toList.take pos)
    let zone := String.ofList (s.toList.drop pos)
    let neg := zone.startsWith "-"
    let zoneBody := String.ofList (zone.toList.drop 1)
    match splitOnChar ':' zoneBody with
    | [h] =>
      match parseNatField h "zone hours" with
      | .ok h => .ok (body, if neg then -(Int.ofNat (h * 3600)) else Int.ofNat (h * 3600))
      | .error e => .error e
    | [h, m] | [h, m, _] =>
      match parseNatField h "zone hours", parseNatField m "zone minutes" with
      | .ok h, .ok m =>
        let secs := Int.ofNat (h * 3600 + m * 60)
        .ok (body, if neg then -secs else secs)
      | .error e, _ => .error e
      | _, .error e => .error e
    | _ => throw s!"bad zone offset {zone}"

instance : PgDecode Timestamp where
  decodeText _ s := do
    rejectInfinity s
    let (body, offsetSecs) ← splitZoneSuffix s
    match splitOnChar ' ' body with
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

/-!
Binary `numeric` is a sequence of big-endian 16-bit fields: digit count,
weight, sign, display scale, then that many base-10000 digits. Both directions
are written as explicit recursion over a `List UInt16` rather than the `for`
loops they replace — a loop body is a `forIn` the kernel cannot unfold, and
`PgNumeric.fromBinary_toBinary` needs to walk the buffer field by field.
-/

/-- A big-endian sequence of 16-bit fields — the whole `numeric` wire shape. -/
def putUInt16s : List UInt16 → ByteArray
  | [] => ByteArray.empty
  | v :: rest => Protocol.putUInt16 ByteArray.empty v ++ putUInt16s rest

/-- The sign-field sentinel PostgreSQL uses for each non-finite value. -/
def PgNumeric.specialSign : PgNumeric.Special → UInt16
  | .nan => 0xC000
  | .posInf => 0xD000
  | .negInf => 0xF000

/-- The wire fields of a `numeric`: the four header words, then the digits.
Special values (NaN, ±Infinity) carry the sentinel sign and no digits. -/
def PgNumeric.wireFields (n : PgNumeric) : List UInt16 :=
  match n.special with
  | some sp => [0, 0, PgNumeric.specialSign sp, 0]
  | none =>
    UInt16.ofNat n.digits.size :: (Int16.ofInt n.weight).toUInt16 ::
      (if n.neg then 0x4000 else 0) :: UInt16.ofNat n.dscale :: n.digits.toList

def PgNumeric.toBinary (n : PgNumeric) : ByteArray := putUInt16s n.wireFields

/-- Read `count` base-10000 digits from `off` onwards, rejecting out-of-range
digits and truncation. Structural recursion on the count. -/
def readNumericDigits (b : ByteArray) :
    Nat → Nat → Array UInt16 → Except String (Array UInt16)
  | _, 0, acc => .ok acc
  | off, count + 1, acc =>
    match Protocol.getUInt16? b off with
    | some d =>
      if d < 10000 then readNumericDigits b (off + 2) count (acc.push d)
      else .error s!"numeric digit {d} out of range"
    | none => .error "truncated numeric digits"

/-- Decode the binary `numeric` representation. A plain match chain (no `do`
binds) so each field read is a single rewrite in the roundtrip proof. -/
def PgNumeric.fromBinary (b : ByteArray) : Except String PgNumeric :=
  match Protocol.getUInt16? b 0, Protocol.getUInt16? b 2,
      Protocol.getUInt16? b 4, Protocol.getUInt16? b 6 with
  | some nd, some wt, some sign, some sc =>
    match sign.toNat with
    | 0xC000 => .ok { special := some .nan }
    | 0xD000 => .ok { special := some .posInf }
    | 0xF000 => .ok { special := some .negInf }
    | s' =>
      if s' == 0 || s' == 0x4000 then
        match readNumericDigits b 8 nd.toInt16.toInt.toNat #[] with
        | .ok digits =>
          .ok { neg := s' == 0x4000, digits, weight := wt.toInt16.toInt,
                dscale := sc.toInt16.toInt.toNat }
        | .error e => .error e
      else .error s!"bad numeric sign {s'}"
  | _, _, _, _ => .error "truncated numeric"

instance : PgDecode PgNumeric where
  decodeText _ s := PgNumeric.fromString s
  decodeBinary _ b := PgNumeric.fromBinary b

instance : PgEncode PgNumeric where
  typeOid := Oid.numeric
  encode n := some n.toString.toUTF8

/-- Binary `interval`: 8-byte microseconds, 4-byte days, 4-byte months
(big-endian, in that order). Shaped as a plain match chain for provability. -/
def PgInterval.fromBinary (b : ByteArray) : Except String PgInterval :=
  if b.size = 16 then
    match rdInt64 b 0, rdInt32 b 8, rdInt32 b 12 with
    | .ok micros, .ok days, .ok months =>
      .ok { months := months.toInt, days := days.toInt, micros := micros.toInt }
    | .error e, _, _ => .error e
    | _, .error e, _ => .error e
    | _, _, .error e => .error e
  else
    .error "interval must be 16 bytes"

instance : PgDecode PgInterval where
  decodeText _ s := PgInterval.fromString s
  decodeBinary _ b := PgInterval.fromBinary b

def PgInterval.toBinary (iv : PgInterval) : ByteArray :=
  putInt64BE (Int64.ofInt iv.micros) ++
    (Protocol.putUInt32 ByteArray.empty (Int32.ofInt iv.days).toUInt32) ++
    (Protocol.putUInt32 ByteArray.empty (Int32.ofInt iv.months).toUInt32)

instance : PgEncode PgInterval where
  typeOid := Oid.interval
  encode iv := some iv.toString.toUTF8

-- ── 1-D arrays ─────────────────────────────────────────────────────────────

/-- Parser state while scanning a 1-D array literal. `buf` holds the current
element's characters in reverse. -/
structure ArrayScan where
  elems : Array (Option String) := #[]
  buf : List Char := []
  /-- The current element was quoted (so `NULL` in it is the literal text). -/
  quoted : Bool := false
  inQuotes : Bool := false
  escaped : Bool := false
  closed : Bool := false
  /-- Something (a character, a quote, or a preceding comma) demands an
  element here, so an empty one is a parse error rather than "no elements". -/
  sawAny : Bool := false
  deriving Inhabited

/-- One scanning step per character. Explicit recursion rather than a `for`
loop with mutable state: a `forIn` body is opaque to the kernel. -/
def arrayScan (src : String) : ArrayScan → List Char → Except String ArrayScan
  | st, [] => .ok st
  | st, c :: rest =>
    if st.closed then .error s!"array: trailing characters in {src}"
    else if st.escaped then
      arrayScan src { st with buf := c :: st.buf, escaped := false } rest
    else if st.inQuotes then
      if c == '\\' then arrayScan src { st with escaped := true } rest
      else if c == '"' then arrayScan src { st with inQuotes := false } rest
      else arrayScan src { st with buf := c :: st.buf } rest
    else if c == '"' then
      arrayScan src { st with inQuotes := true, quoted := true, sawAny := true } rest
    else if c == ',' || c == '}' then
      let text := String.ofList st.buf.reverse
      if st.sawAny || !text.isEmpty then
        arrayScan src
          { st with
            elems := st.elems.push (if !st.quoted && text == "NULL" then none else some text)
            buf := [], quoted := false, sawAny := c == ',', closed := c == '}' } rest
      else if c == ',' then .error s!"array: empty element in {src}"
      else
        arrayScan src
          { st with buf := [], quoted := false, sawAny := c == ',', closed := c == '}' } rest
    else arrayScan src { st with buf := c :: st.buf, sawAny := true } rest

/-- Parse `{a,"quo\"ted",NULL}` into raw element texts. 1-D only. -/
def parseArrayText (s : String) : Except String (Array (Option String)) :=
  match trimAsciiChars s.toList with
  | '{' :: rest =>
    match arrayScan s {} rest with
    | .error e => .error e
    | .ok st =>
      if st.closed && !st.inQuotes && !st.escaped then .ok st.elems
      else .error s!"array: unterminated {s}"
  | _ => .error s!"not an array literal: {s}"

/-- Escape `"` and `\` inside a quoted array element. -/
def escapeArrayChars : List Char → List Char
  | [] => []
  | c :: rest =>
    if c == '"' || c == '\\' then '\\' :: c :: escapeArrayChars rest
    else c :: escapeArrayChars rest

/-- One element of an array literal: the unquoted word `NULL`, or the element
text in double quotes. Non-NULL elements are *always* quoted, so an element
whose text is literally `NULL` survives the roundtrip. -/
def arrayElemChars : Option String → List Char
  | none => ['N', 'U', 'L', 'L']
  | some t => '"' :: (escapeArrayChars t.toList ++ ['"'])

/-- The elements and closing brace of a 1-D array literal. -/
def arrayBodyChars : List (Option String) → List Char
  | [] => ['}']
  | [e] => arrayElemChars e ++ ['}']
  | e :: rest => arrayElemChars e ++ ',' :: arrayBodyChars rest

/-- `{"a","b",NULL}` — the literal PostgreSQL accepts for a 1-D array
parameter of any element type (the server casts each quoted element). -/
def renderArrayText (elems : List (Option String)) : String :=
  String.ofList ('{' :: arrayBodyChars elems)

/-- Send a 1-D array as a text parameter; `none` elements become SQL NULL. -/
instance : PgEncode (Array (Option String)) where
  encode a := some (renderArrayText a.toList).toUTF8

/-- Read `count` length-prefixed binary array elements starting at `off`.
Explicit recursion on the count. -/
def decodeArrayElems (α : Type) [PgDecode α] (elemOid : UInt32) (b : ByteArray) :
    Nat → Nat → Array α → Except String (Array α)
  | _, 0, out => .ok out
  | off, count + 1, out =>
    match rdInt32 b off with
    | .error e => .error e
    | .ok len32 =>
      if len32.toInt == -1 then
        match PgDecode.decodeNull (α := α) with
        | .ok v => decodeArrayElems α elemOid b (off + 4) count (out.push v)
        | .error e => .error e
      else
        let n := len32.toInt.toNat
        if off + 4 + n ≤ b.size then
          match PgDecode.decodeBinary (α := α) elemOid (b.extract (off + 4) (off + 4 + n)) with
          | .ok v => decodeArrayElems α elemOid b (off + 4 + n) count (out.push v)
          | .error e => .error e
        else .error "truncated array element"

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
    decodeArrayElems α elemOid b 20 count #[]

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

/-!
### Binary integer roundtrips

The big-endian binary writers and readers invert each other:
`rdInt16`/`rdInt32`/`rdInt64`/`rdUInt64` read back exactly what
`putUInt16`/`putInt32`/`putInt64BE` wrote, and the width-dispatching
`rdIntAny` recovers the mathematical integer at every width.
-/

/-- Disjoint or/add: `b` occupies strictly the low `i` bits, `a * 2 ^ i` only
bits at or above `i`, so the two combine additively. (`Pg.Protocol` has the
same helper for the 16/32-bit widths; it is `private` there.) -/
private theorem or_add_lt {a b i : Nat} (hb : b < 2 ^ i) :
    a * 2 ^ i ||| b = a * 2 ^ i + b := by
  rw [show a * 2 ^ i = a <<< i from (Nat.shiftLeft_eq a i).symm,
    ← Nat.shiftLeft_add_eq_or_of_lt hb]

/-- The numeric value of a big-endian pair of `UInt32` halves. -/
private theorem pack_nat64 (hi lo : UInt32) :
    (hi.toUInt64 <<< 32 ||| lo.toUInt64).toNat = hi.toNat * 2 ^ 32 + lo.toNat := by
  have h0 := hi.toNat_lt
  have h1 := lo.toNat_lt
  simp only [UInt64.toNat_or, UInt64.toNat_shiftLeft, UInt32.toNat_toUInt64,
    show UInt64.toNat 32 % 64 = 32 from rfl, Nat.shiftLeft_eq]
  rw [show hi.toNat * 2 ^ 32 % 2 ^ 64 = hi.toNat * 2 ^ 32 from by omega,
    or_add_lt (i := 32)]
  omega

/-- Splitting a `UInt64` into big-endian `UInt32` halves and repacking is the
identity — the 64-bit counterpart of `Pg.Protocol.pack_unpack`, proved by
`omega` over `Nat` rather than by an LRAT certificate. -/
private theorem unpack_pack64 (u : UInt64) :
    (u >>> 32).toUInt32.toUInt64 <<< 32 ||| u.toUInt32.toUInt64 = u := by
  apply UInt64.toNat_inj.mp
  rw [pack_nat64]
  have hv := u.toNat_lt
  simp only [UInt64.toNat_toUInt32, UInt64.toNat_shiftRight,
    show UInt64.toNat 32 % 64 = 32 from rfl, Nat.shiftRight_eq_div_pow]
  omega

theorem size_putInt64BE (v : Int64) : (putInt64BE v).size = 8 := by
  unfold putInt64BE
  rw [Protocol.size_putUInt32, Protocol.size_putUInt32, ByteArray.size_empty]

theorem putInt64BE_split (v : Int64) :
    putInt64BE v =
      Protocol.putUInt32 ByteArray.empty (v.toUInt64 >>> 32).toUInt32 ++
        Protocol.putUInt32 ByteArray.empty v.toUInt64.toUInt32 :=
  Protocol.putUInt32_append _ _

theorem getUInt32?_putInt64BE_0 (v : Int64) :
    Protocol.getUInt32? (putInt64BE v) 0 = some (v.toUInt64 >>> 32).toUInt32 := by
  rw [putInt64BE_split,
    Protocol.getUInt32?_append_left
      (by rw [Protocol.size_putUInt32, ByteArray.size_empty]; omega),
    Protocol.getUInt32?_putUInt32]

theorem getUInt32?_putInt64BE_4 (v : Int64) :
    Protocol.getUInt32? (putInt64BE v) 4 = some v.toUInt64.toUInt32 := by
  have hA : (Protocol.putUInt32 ByteArray.empty (v.toUInt64 >>> 32).toUInt32).size = 4 := by
    rw [Protocol.size_putUInt32, ByteArray.size_empty]
  rw [putInt64BE_split, Protocol.getUInt32?_append_right (by omega),
    show 4 - (Protocol.putUInt32 ByteArray.empty (v.toUInt64 >>> 32).toUInt32).size = 0
      by omega,
    Protocol.getUInt32?_putUInt32]

theorem rdInt16_putUInt16 (x : Int16) :
    rdInt16 (Protocol.putUInt16 ByteArray.empty x.toUInt16) = .ok x := by
  unfold rdInt16
  simp only [Protocol.getUInt16?_putUInt16, Int16.toInt16_toUInt16]
  rfl

theorem rdInt32_putInt32 (x : Int32) :
    rdInt32 (Protocol.putInt32 ByteArray.empty x) = .ok x := by
  unfold rdInt32
  rw [Protocol.putInt32_eq]
  simp only [Protocol.getUInt32?_putUInt32, Int32.toInt32_toUInt32]
  rfl

theorem rdUInt64_putInt64BE (v : Int64) : rdUInt64 (putInt64BE v) = .ok v.toUInt64 := by
  unfold rdUInt64
  simp only [Nat.zero_add, getUInt32?_putInt64BE_0, getUInt32?_putInt64BE_4]
  exact congrArg Except.ok (unpack_pack64 v.toUInt64)

theorem rdInt64_putInt64BE (v : Int64) : rdInt64 (putInt64BE v) = .ok v := by
  unfold rdInt64
  rw [rdUInt64_putInt64BE]
  show Except.ok v.toUInt64.toInt64 = Except.ok v
  rw [Int64.toInt64_toUInt64]

/-- `rdIntAny` recovers the integer from an 8-byte big-endian encoding. -/
theorem rdIntAny_putInt64BE (v : Int64) : rdIntAny (putInt64BE v) = .ok v.toInt := by
  unfold rdIntAny
  rw [size_putInt64BE, rdInt64_putInt64BE]
  rfl

/-- `rdIntAny` recovers the integer from a 2-byte big-endian encoding. -/
theorem rdIntAny_putUInt16 (x : Int16) :
    rdIntAny (Protocol.putUInt16 ByteArray.empty x.toUInt16) = .ok x.toInt := by
  unfold rdIntAny
  rw [Protocol.size_putUInt16, ByteArray.size_empty, Nat.zero_add, rdInt16_putUInt16]
  rfl

/-- `rdIntAny` recovers the integer from a 4-byte big-endian encoding. -/
theorem rdIntAny_putInt32 (x : Int32) :
    rdIntAny (Protocol.putInt32 ByteArray.empty x) = .ok x.toInt := by
  unfold rdIntAny
  rw [Protocol.size_putInt32, ByteArray.size_empty, Nat.zero_add, rdInt32_putInt32]
  rfl

/-- Every representable `interval` (fields within int32/int64 wire range)
roundtrips through its 16-byte binary form. -/
theorem PgInterval.fromBinary_toBinary (m d : Int32) (u : Int64) :
    PgInterval.fromBinary
        (PgInterval.toBinary { months := m.toInt, days := d.toInt, micros := u.toInt }) =
      .ok { months := m.toInt, days := d.toInt, micros := u.toInt } := by
  have hb : PgInterval.toBinary { months := m.toInt, days := d.toInt, micros := u.toInt } =
      putInt64BE u ++
        (Protocol.putUInt32 ByteArray.empty d.toUInt32 ++
          Protocol.putUInt32 ByteArray.empty m.toUInt32) := by
    unfold PgInterval.toBinary
    rw [Int64.ofInt_toInt, Int32.ofInt_toInt, Int32.ofInt_toInt, ByteArray.append_assoc]
  suffices h : ∀ b : ByteArray,
      b = putInt64BE u ++
        (Protocol.putUInt32 ByteArray.empty d.toUInt32 ++
          Protocol.putUInt32 ByteArray.empty m.toUInt32) →
      PgInterval.fromBinary b =
        .ok { months := m.toInt, days := d.toInt, micros := u.toInt } by
    rw [hb]
    exact h _ rfl
  intro b hbdef
  have hP : (putInt64BE u).size = 8 := size_putInt64BE u
  have hD : (Protocol.putUInt32 ByteArray.empty d.toUInt32).size = 4 := by
    rw [Protocol.size_putUInt32, ByteArray.size_empty]
  have hM : (Protocol.putUInt32 ByteArray.empty m.toUInt32).size = 4 := by
    rw [Protocol.size_putUInt32, ByteArray.size_empty]
  have hsize : b.size = 16 := by
    rw [hbdef, ByteArray.size_append, ByteArray.size_append, hP, hD, hM]
  have h0 : Protocol.getUInt32? b 0 = some (u.toUInt64 >>> 32).toUInt32 := by
    rw [hbdef, Protocol.getUInt32?_append_left (by omega), getUInt32?_putInt64BE_0]
  have h4 : Protocol.getUInt32? b 4 = some u.toUInt64.toUInt32 := by
    rw [hbdef, Protocol.getUInt32?_append_left (by omega), getUInt32?_putInt64BE_4]
  have h8 : Protocol.getUInt32? b 8 = some d.toUInt32 := by
    rw [hbdef, Protocol.getUInt32?_append_right (by omega),
      show 8 - (putInt64BE u).size = 0 by omega,
      Protocol.getUInt32?_append_left (by omega), Protocol.getUInt32?_putUInt32]
  have h12 : Protocol.getUInt32? b 12 = some m.toUInt32 := by
    rw [hbdef, Protocol.getUInt32?_append_right (by omega),
      show 12 - (putInt64BE u).size = 4 by omega,
      Protocol.getUInt32?_append_right (by omega),
      show 4 - (Protocol.putUInt32 ByteArray.empty d.toUInt32).size = 0 by omega,
      Protocol.getUInt32?_putUInt32]
  have hrd64 : rdInt64 b 0 = .ok u := by
    unfold rdInt64 rdUInt64
    simp only [Nat.zero_add, h0, h4]
    show Except.ok ((u.toUInt64 >>> 32).toUInt32.toUInt64 <<< 32 |||
      u.toUInt64.toUInt32.toUInt64).toInt64 = Except.ok u
    rw [unpack_pack64 u.toUInt64, Int64.toInt64_toUInt64]
  have hrd8 : rdInt32 b 8 = .ok d := by
    unfold rdInt32
    simp only [h8, Int32.toInt32_toUInt32]
    rfl
  have hrd12 : rdInt32 b 12 = .ok m := by
    unfold rdInt32
    simp only [h12, Int32.toInt32_toUInt32]
    rfl
  unfold PgInterval.fromBinary
  rw [hsize, if_pos rfl, hrd64, hrd8, hrd12]

/-!
### Temporal text roundtrips

PostgreSQL renders `date` and `time` as fixed-width decimal fields; these laws
say pg-lean's parser recovers exactly what its renderer wrote. Floats are
deliberately absent: `toString`/`parseFloat` is *not* an unconditional IEEE-754
roundtrip (shortest-representation printing plus decimal-to-binary rounding),
and stating the true law needs real-arithmetic support this repository does not
have (core + Std only, no Mathlib).
-/

/-- **A rendered date parses back to its own three fields.** -/
theorem dateFields_renderDate {d : PlainDate} (hyear : 0 ≤ d.year) :
    dateFields (renderDate d) = .ok (d.year.natAbs, d.month.toNat, d.day.toNat) := by
  have hdash : isAsciiDigit '-' = false := by decide
  have hchars : dateChars d = padDigits 4 d.year.natAbs ++
      '-' :: (padDigits 2 d.month.toNat ++ '-' :: padDigits 2 d.day.toNat) := by
    unfold dateChars yearChars
    split
    · rename_i hc; exact absurd hyear (Int.not_le.mpr hc)
    · rfl
  unfold dateFields renderDate
  rw [hchars, splitOnChar_cons (not_mem_padDigits hdash),
    splitOnChar_cons (not_mem_padDigits hdash),
    splitOnChar_singleton (by rw [String.toList_ofList]; exact not_mem_padDigits hdash)]
  simp only [parseNatField_padDigits]

theorem month_ofInt_toNat (m : Std.Time.Month.Ordinal) :
    Std.Time.Internal.Bounded.LE.ofInt (Int.ofNat m.toNat) = some m := by
  obtain ⟨v, hv⟩ := m
  cases v with
  | ofNat k =>
    show Std.Time.Internal.Bounded.LE.ofInt (Int.ofNat k) = _
    unfold Std.Time.Internal.Bounded.LE.ofInt
    rw [dif_pos hv]
    rfl
  | negSucc k => exact absurd hv.1 (by omega)

theorem day_ofInt_toNat (d : Std.Time.Day.Ordinal) :
    Std.Time.Internal.Bounded.LE.ofInt (Int.ofNat d.toNat) = some d := by
  obtain ⟨v, hv⟩ := d
  cases v with
  | ofNat k =>
    show Std.Time.Internal.Bounded.LE.ofInt (Int.ofNat k) = _
    unfold Std.Time.Internal.Bounded.LE.ofInt
    rw [dif_pos hv]
    rfl
  | negSucc k => exact absurd hv.1 (by omega)

/-- **A rendered `date` parses back to the same `PlainDate`** (AD dates: BC
years render with a leading `-`, which PostgreSQL spells `... BC` and pg-lean
does not accept). -/
theorem parseDate_renderDate {d : PlainDate} (hyear : 0 ≤ d.year) :
    parseDate (renderDate d) = .ok d := by
  have hnat : Int.ofNat d.year.natAbs = d.year := Int.natAbs_of_nonneg hyear
  unfold parseDate
  rw [dateFields_renderDate hyear]
  simp only [month_ofInt_toNat, day_ofInt_toNat, hnat]
  unfold PlainDate.ofYearMonthDay?
  rw [dif_pos d.valid]

theorem fracNanos_padDigits {x : Nat} (hx : x < 1000000) :
    fracNanos (String.ofList (padDigits 6 x)) = .ok (x * 1000) := by
  have hlen : (padDigits 6 x).length = 6 :=
    padDigits_length (by have := natDigits_length_le 5 x (by simpa using hx); omega)
  have hne : (String.ofList (padDigits 6 x)).isEmpty = false := by
    refine String.isEmpty_eq_false_iff.mpr (fun hc => ?_)
    have hto := congrArg String.toList hc
    rw [String.toList_ofList] at hto
    exact absurd (hto.trans (by rfl)) (padDigits_ne_nil 6 x)
  unfold fracNanos
  rw [if_neg (by simp [hne]), String.toList_ofList,
    show List.take 9 (padDigits 6 x ++ List.replicate 9 '0')
        = padDigits 6 x ++ List.replicate 3 '0' from by
      rw [List.take_append, hlen, List.take_of_length_le (by omega), List.take_replicate]
      rfl]
  unfold parseNatField
  rw [String.toList_ofList]
  have hval : natOfDigits 0 (padDigits 6 x ++ List.replicate 3 '0') = some (x * 1000) := by
    rw [natOfDigits_append, natOfDigits_padDigits, Option.bind_some, natOfDigits_zeros]
  cases hp : padDigits 6 x ++ List.replicate 3 '0' with
  | nil => exact absurd (List.append_eq_nil_iff.mp hp).1 (padDigits_ne_nil 6 x)
  | cons a t =>
    rw [hp] at hval
    rw [show natOfDigitsFull (a :: t) = some (x * 1000) from hval]
    rfl

/-- `HH:MM:SS` fields render and parse back, whatever the fraction carries. -/
theorem hmsNanos_render {h m sec : Nat} (hh : h < 24) (hm : m < 60) (hs : sec < 61)
    {frac : String} {f : Nat} (hf : fracNanos frac = .ok f) :
    hmsNanos
        (String.ofList (padDigits 2 h ++ ':' :: (padDigits 2 m ++ ':' :: padDigits 2 sec)))
        frac
      = .ok (Int.ofNat (((h * 3600 + m * 60 + sec) * 1000000000) + f)) := by
  have hcolon : isAsciiDigit ':' = false := by decide
  unfold hmsNanos
  rw [splitOnChar_cons (not_mem_padDigits hcolon),
    splitOnChar_cons (not_mem_padDigits hcolon),
    splitOnChar_singleton (by rw [String.toList_ofList]; exact not_mem_padDigits hcolon)]
  simp only [parseNatField_padDigits, hf]
  rw [if_pos (by simp only [Bool.and_eq_true, decide_eq_true_eq]; exact ⟨⟨hh, hm⟩, hs⟩)]

/-- **A rendered time-of-day parses back to the same nanosecond count**, at
PostgreSQL's microsecond resolution (`time` stores microseconds, so a value
with sub-microsecond nanoseconds cannot survive any text form). -/
theorem parseTimeNanos_renderTimeNanos {n : Nat} (hlt : n < 86400000000000)
    (hmicro : n % 1000 = 0) :
    parseTimeNanos (renderTimeNanos n) = .ok (Int.ofNat n) := by
  have hdot : isAsciiDigit '.' = false := by decide
  have hh : n / 1000000000 / 3600 < 24 := by omega
  have hm : n / 1000000000 / 60 % 60 < 60 := by omega
  have hs : n / 1000000000 % 60 < 61 := by omega
  by_cases hsub : n % 1000000000 = 0
  · have hchars : timeChars n = padDigits 2 (n / 1000000000 / 3600) ++
        ':' :: (padDigits 2 (n / 1000000000 / 60 % 60) ++
          ':' :: padDigits 2 (n / 1000000000 % 60)) := by
      unfold timeChars
      rw [if_pos (by simp [hsub]), List.append_nil]
    have hstep := hmsNanos_render hh hm hs (frac := "") (f := 0) rfl
    unfold parseTimeNanos renderTimeNanos
    rw [hchars,
      splitOnChar_singleton (by
        rw [String.toList_ofList]
        simp only [List.mem_append, List.mem_cons, not_or]
        exact ⟨not_mem_padDigits hdot, by decide, not_mem_padDigits hdot, by decide,
          not_mem_padDigits hdot⟩)]
    refine hstep.trans ?_
    congr 1
    exact congrArg Int.ofNat (by omega)
  · have hchars : timeChars n =
        (padDigits 2 (n / 1000000000 / 3600) ++
          ':' :: (padDigits 2 (n / 1000000000 / 60 % 60) ++
            ':' :: padDigits 2 (n / 1000000000 % 60))) ++
          '.' :: padDigits 6 (n % 1000000000 / 1000) := by
      unfold timeChars
      rw [if_neg (by simp [hsub])]
      simp [List.append_assoc]
    have hstep := hmsNanos_render hh hm hs
      (fracNanos_padDigits (x := n % 1000000000 / 1000) (by omega))
    unfold parseTimeNanos renderTimeNanos
    rw [hchars,
      splitOnChar_cons (by
        simp only [List.mem_append, List.mem_cons, not_or]
        exact ⟨not_mem_padDigits hdot, by decide, not_mem_padDigits hdot, by decide,
          not_mem_padDigits hdot⟩),
      splitOnChar_singleton (by rw [String.toList_ofList]; exact not_mem_padDigits hdot)]
    refine hstep.trans ?_
    congr 1
    exact congrArg Int.ofNat (by omega)

theorem not_mem_dateChars {sep : Char} (hsep : isAsciiDigit sep = false)
    (hdash : sep ≠ '-') (d : PlainDate) : sep ∉ dateChars d := by
  unfold dateChars yearChars
  simp only [List.mem_append, List.mem_cons, not_or]
  refine ⟨?_, hdash, not_mem_padDigits hsep, hdash, not_mem_padDigits hsep⟩
  split
  · simp only [List.mem_cons, not_or]
    exact ⟨hdash, not_mem_padDigits hsep⟩
  · exact not_mem_padDigits hsep

theorem not_mem_timeChars {sep : Char} (hsep : isAsciiDigit sep = false)
    (hcolon : sep ≠ ':') (hdot : sep ≠ '.') (n : Nat) : sep ∉ timeChars n := by
  unfold timeChars
  simp only [List.mem_append, List.mem_cons, not_or]
  refine ⟨not_mem_padDigits hsep, hcolon, not_mem_padDigits hsep, hcolon,
    not_mem_padDigits hsep, ?_⟩
  split
  · exact List.not_mem_nil
  · simp only [List.mem_cons, not_or]
    exact ⟨hdot, not_mem_padDigits hsep⟩

/-- **A rendered timestamp splits back into the same date and the same
nanoseconds-since-midnight.** (Turning those nanoseconds into a `PlainTime`
is `Std.Time`'s `ofNanoseconds`, which this repository does not reason
about.) -/
theorem timestampFields_renderTimestamp {d : PlainDate} {n : Nat}
    (hyear : 0 ≤ d.year) (hlt : n < 86400000000000) (hmicro : n % 1000 = 0) :
    timestampFields (renderTimestamp d n) = .ok (d, Int.ofNat n) := by
  have hspace : isAsciiDigit ' ' = false := by decide
  unfold timestampFields renderTimestamp
  rw [splitOnChar_cons (not_mem_dateChars hspace (by decide) d),
    splitOnChar_singleton (by
      rw [String.toList_ofList]
      exact not_mem_timeChars hspace (by decide) (by decide) n)]
  simp only [show String.ofList (dateChars d) = renderDate d from rfl,
    show String.ofList (timeChars n) = renderTimeNanos n from rfl,
    parseDate_renderDate hyear, parseTimeNanos_renderTimeNanos hlt hmicro]

/-!
### 1-D array literals

`renderArrayText` quotes every non-NULL element, so `parseArrayText` recovers
the element list exactly — including an element whose text is the word `NULL`,
and including embedded quotes and backslashes.
-/

/-- Scanning a quoted element body: the escapes come back off. -/
theorem arrayScan_quoted (src : String) : ∀ (body : List Char)
    (acc : Array (Option String)) (buf : List Char) (any : Bool) (rest : List Char),
    arrayScan src (ArrayScan.mk acc buf true true false false any)
        (escapeArrayChars body ++ '"' :: rest)
      = arrayScan src (ArrayScan.mk acc (body.reverse ++ buf) true false false false any)
          rest := by
  intro body
  induction body with
  | nil =>
    intro acc buf any rest
    simp [escapeArrayChars, arrayScan]
  | cons c t ih =>
    intro acc buf any rest
    by_cases hc : (c == '"' || c == '\\') = true
    · rw [show escapeArrayChars (c :: t) = '\\' :: c :: escapeArrayChars t from by
        rw [escapeArrayChars, if_pos hc]]
      rw [show ('\\' :: c :: escapeArrayChars t) ++ '"' :: rest
          = '\\' :: (c :: (escapeArrayChars t ++ '"' :: rest)) from rfl]
      rw [show arrayScan src (ArrayScan.mk acc buf true true false false any)
          ('\\' :: (c :: (escapeArrayChars t ++ '"' :: rest)))
          = arrayScan src (ArrayScan.mk acc buf true true true false any)
            (c :: (escapeArrayChars t ++ '"' :: rest)) from by simp [arrayScan]]
      rw [show arrayScan src (ArrayScan.mk acc buf true true true false any)
          (c :: (escapeArrayChars t ++ '"' :: rest))
          = arrayScan src (ArrayScan.mk acc (c :: buf) true true false false any)
            (escapeArrayChars t ++ '"' :: rest) from by simp [arrayScan]]
      rw [ih acc (c :: buf) any rest]
      simp
    · have hq : (c == '"') = false := Bool.eq_false_iff.mpr (fun h => hc (by simp [h]))
      have hb : (c == '\\') = false := Bool.eq_false_iff.mpr (fun h => hc (by simp [h]))
      rw [show escapeArrayChars (c :: t) = c :: escapeArrayChars t from by
        rw [escapeArrayChars, if_neg hc]]
      rw [show (c :: escapeArrayChars t) ++ '"' :: rest
          = c :: (escapeArrayChars t ++ '"' :: rest) from rfl]
      rw [show arrayScan src (ArrayScan.mk acc buf true true false false any)
          (c :: (escapeArrayChars t ++ '"' :: rest))
          = arrayScan src (ArrayScan.mk acc (c :: buf) true true false false any)
            (escapeArrayChars t ++ '"' :: rest) from by simp [arrayScan, hq, hb]]
      rw [ih acc (c :: buf) any rest]
      simp

/-- One rendered element is scanned into one pushed element. -/
theorem arrayScan_elem (src : String) (e : Option String) (acc : Array (Option String))
    (any : Bool) (sep : Char) (rest : List Char)
    (hcomma : (sep == ',') = true ∨ (sep == '}') = true) :
    arrayScan src (ArrayScan.mk acc [] false false false false any)
        (arrayElemChars e ++ sep :: rest)
      = arrayScan src
          (ArrayScan.mk (acc.push e) [] false false false (sep == '}') (sep == ',')) rest := by
  have hsep : (sep == ',' || sep == '}') = true := by
    rcases hcomma with h | h <;> simp [h]
  have hquote : (sep == '"') = false := by
    rcases hcomma with h | h <;> (rw [eq_of_beq h]; rfl)
  cases e with
  | none =>
    show arrayScan src (ArrayScan.mk acc [] false false false false any)
      ('N' :: 'U' :: 'L' :: 'L' :: sep :: rest) = _
    simp [arrayScan, hsep, hquote]
  | some t =>
    show arrayScan src (ArrayScan.mk acc [] false false false false any)
      ('"' :: (escapeArrayChars t.toList ++ ['"'] ++ sep :: rest)) = _
    rw [show escapeArrayChars t.toList ++ ['"'] ++ sep :: rest
        = escapeArrayChars t.toList ++ '"' :: sep :: rest from by simp]
    rw [show arrayScan src (ArrayScan.mk acc [] false false false false any)
        ('"' :: (escapeArrayChars t.toList ++ '"' :: sep :: rest))
        = arrayScan src (ArrayScan.mk acc [] true true false false true)
          (escapeArrayChars t.toList ++ '"' :: sep :: rest) from by simp [arrayScan]]
    rw [arrayScan_quoted src t.toList acc [] true (sep :: rest)]
    simp [arrayScan, hsep, hquote]

/-- Every array body ends with the closing brace. -/
theorem arrayBodyChars_snoc : ∀ es : List (Option String),
    ∃ pre, arrayBodyChars es = pre ++ ['}'] := by
  intro es
  induction es with
  | nil => exact ⟨[], rfl⟩
  | cons e t ih =>
    cases t with
    | nil => exact ⟨arrayElemChars e, rfl⟩
    | cons e' t' =>
      obtain ⟨pre, hpre⟩ := ih
      exact ⟨arrayElemChars e ++ ',' :: pre, by
        rw [show arrayBodyChars (e :: e' :: t')
            = arrayElemChars e ++ ',' :: arrayBodyChars (e' :: t') from rfl, hpre]
        simp⟩

theorem trimAsciiChars_bracketed (mid : List Char) :
    trimAsciiChars ('{' :: (mid ++ ['}'])) = '{' :: (mid ++ ['}']) := by
  unfold trimAsciiChars
  rw [List.dropWhile_cons, if_neg (by decide)]
  have hrev : ('{' :: (mid ++ ['}'])).reverse = '}' :: (mid.reverse ++ ['{']) := by simp
  rw [hrev, List.dropWhile_cons, if_neg (by decide)]
  simp

/-- Scanning the whole body of a non-empty array literal. -/
theorem arrayScan_body (src : String) : ∀ (es : List (Option String)) (e : Option String)
    (acc : Array (Option String)) (any : Bool),
    arrayScan src (ArrayScan.mk acc [] false false false false any)
        (arrayBodyChars (e :: es))
      = .ok (ArrayScan.mk (acc ++ (e :: es).toArray) [] false false false true false) := by
  intro es
  induction es with
  | nil =>
    intro e acc any
    rw [show arrayBodyChars [e] = arrayElemChars e ++ '}' :: [] from rfl,
      arrayScan_elem src e acc any '}' [] (Or.inr rfl)]
    simp [arrayScan]
  | cons e' t ih =>
    intro e acc any
    rw [show arrayBodyChars (e :: e' :: t)
        = arrayElemChars e ++ ',' :: arrayBodyChars (e' :: t) from rfl,
      arrayScan_elem src e acc any ',' _ (Or.inl rfl),
      show ((',' : Char) == '}') = false from rfl, show ((',' : Char) == ',') = true from rfl,
      ih e' (acc.push e) true]
    simp

/-- **A rendered 1-D array parses back to the same elements**, NULLs included —
and an element whose text is literally `NULL` stays a value, because every
non-NULL element is quoted. -/
theorem parseArrayText_renderArrayText (es : List (Option String)) :
    parseArrayText (renderArrayText es) = .ok es.toArray := by
  obtain ⟨pre, hpre⟩ := arrayBodyChars_snoc es
  unfold parseArrayText renderArrayText
  rw [String.toList_ofList, hpre, trimAsciiChars_bracketed, ← hpre]
  cases es with
  | nil => rfl
  | cons e t =>
    simp only [arrayScan_body (String.ofList ('{' :: arrayBodyChars (e :: t))) t e #[] false]
    simp

/-- An `Array.mapM` whose function never fails and returns its argument
succeeds with that array. Core has `Array.mapM_pure` for a syntactically pure
function; the element decoder is a `match`, so route through `funext`. -/
private theorem mapM_ok_of_pure {α ε : Type} (f : α → Except ε α)
    (a : Array α) (h : ∀ x, f x = .ok x) : a.mapM f = .ok a := by
  have hf : f = fun x => pure (id x) := funext h
  rw [hf, Array.mapM_pure, Array.map_id]
  rfl

/-- **The 1-D array roundtrip at the public API.** Whatever array of element
texts (NULLs included) the client sends as a text parameter, `decodeValue`
reads back as the same array. This is `parseArrayText_renderArrayText` lifted
through the `PgDecode (Array α)` instance's per-element `mapM`. -/
theorem decode_encode_array (oid : UInt32) (a : Array (Option String)) :
    decodeValue (α := Array (Option String)) oid
      (PgEncode.format (Array (Option String))) (PgEncode.encode a) = .ok a := by
  show decodeValue oid 0 (some (renderArrayText a.toList).toUTF8) = .ok a
  rw [decodeValue_text]
  show (do
    let elems ← parseArrayText (renderArrayText a.toList)
    elems.mapM fun
      | none => PgDecode.decodeNull
      | some t => PgDecode.decodeText (Oid.arrayElem oid) t) = .ok a
  rw [parseArrayText_renderArrayText, Array.toArray_toList]
  show a.mapM (fun x =>
    match x with
    | none => PgDecode.decodeNull
    | some t => PgDecode.decodeText (Oid.arrayElem oid) t) = .ok a
  exact mapM_ok_of_pure _ a (fun x => by cases x <;> rfl)

/-!
### `numeric`: the lossless base-10000 roundtrip

`numeric` is the type where a silent precision bug would be worst — it is
PostgreSQL's exact decimal, and pg-lean keeps the server's own representation
verbatim rather than converting through a float. These laws say the binary
form is faithful: every field and every base-10000 digit comes back unchanged.
-/

theorem size_putUInt16s : ∀ l : List UInt16, (putUInt16s l).size = 2 * l.length := by
  intro l
  induction l with
  | nil => rfl
  | cons v t ih =>
    simp only [putUInt16s, ByteArray.size_append, ih, Protocol.size_putUInt16,
      ByteArray.size_empty, List.length_cons]
    omega

theorem putUInt16s_append : ∀ a b : List UInt16,
    putUInt16s (a ++ b) = putUInt16s a ++ putUInt16s b := by
  intro a b
  induction a with
  | nil => simp only [List.nil_append, putUInt16s, ByteArray.empty_append]
  | cons v t ih => simp only [List.cons_append, putUInt16s, ih, ByteArray.append_assoc]

/-- Field `i` of a written 16-bit sequence reads back as itself, at any offset
into a preceding buffer. This one lemma serves both the four header words and
the digits. -/
theorem getUInt16?_putUInt16s : ∀ (l : List UInt16) (pre : ByteArray) (i : Nat)
    (h : i < l.length),
    Protocol.getUInt16? (pre ++ putUInt16s l) (pre.size + 2 * i) = some l[i] := by
  intro l
  induction l with
  | nil => intro pre i h; exact absurd h (by simp)
  | cons v t ih =>
    intro pre i h
    have hp : (pre ++ Protocol.putUInt16 ByteArray.empty v).size = pre.size + 2 := by
      rw [ByteArray.size_append, Protocol.size_putUInt16, ByteArray.size_empty]
    cases i with
    | zero =>
      simp only [putUInt16s, ← ByteArray.append_assoc, Nat.mul_zero, Nat.add_zero,
        List.getElem_cons_zero]
      rw [Protocol.getUInt16?_append_left (by omega),
        Protocol.getUInt16?_append_right (Nat.le_refl _), Nat.sub_self,
        Protocol.getUInt16?_putUInt16]
    | succ j =>
      have hih := ih (pre ++ Protocol.putUInt16 ByteArray.empty v) j
        (by simp only [List.length_cons] at h; omega)
      rw [hp] at hih
      simp only [putUInt16s, ← ByteArray.append_assoc, List.getElem_cons_succ]
      rw [show pre.size + 2 * (j + 1) = pre.size + 2 + 2 * j from by omega]
      exact hih

/-- The digit reader recovers exactly the digits that were written. -/
theorem readNumericDigits_putUInt16s : ∀ (ds : List UInt16) (pre : ByteArray)
    (acc : Array UInt16), (∀ d ∈ ds, d < 10000) →
    readNumericDigits (pre ++ putUInt16s ds) pre.size ds.length acc
      = .ok (acc ++ ds.toArray) := by
  intro ds
  induction ds with
  | nil =>
    intro pre acc _
    show Except.ok acc = Except.ok (acc ++ (List.nil (α := UInt16)).toArray)
    exact congrArg Except.ok (Array.append_empty (xs := acc)).symm
  | cons d t ih =>
    intro pre acc hlt
    have hp : (pre ++ Protocol.putUInt16 ByteArray.empty d).size = pre.size + 2 := by
      rw [ByteArray.size_append, Protocol.size_putUInt16, ByteArray.size_empty]
    have hhead : Protocol.getUInt16? (pre ++ putUInt16s (d :: t)) pre.size = some d := by
      have := getUInt16?_putUInt16s (d :: t) pre 0 (by simp)
      simpa using this
    have hih := ih (pre ++ Protocol.putUInt16 ByteArray.empty d) (acc.push d)
      (fun x hx => hlt x (List.mem_cons_of_mem _ hx))
    rw [hp] at hih
    have hsplit : pre ++ putUInt16s (d :: t)
        = (pre ++ Protocol.putUInt16 ByteArray.empty d) ++ putUInt16s t := by
      show pre ++ (Protocol.putUInt16 ByteArray.empty d ++ putUInt16s t) = _
      rw [ByteArray.append_assoc]
    rw [← hsplit] at hih
    simp only [List.length_cons, readNumericDigits, hhead,
      if_pos (hlt d (List.mem_cons_self ..)), hih]
    exact congrArg Except.ok List.push_append_toArray

/-- A field of a written 16-bit sequence, read at its own offset from the front
of a longer buffer. -/
theorem getUInt16?_putUInt16s_prefix (l : List UInt16) (rest : ByteArray) (i : Nat)
    (h : i < l.length) :
    Protocol.getUInt16? (putUInt16s l ++ rest) (2 * i) = some l[i] := by
  rw [Protocol.getUInt16?_append_left (by rw [size_putUInt16s]; omega)]
  have := getUInt16?_putUInt16s l ByteArray.empty i h
  rw [ByteArray.empty_append, ByteArray.size_empty, Nat.zero_add] at this
  exact this

/-- A field of a written 16-bit sequence, read from the buffer it alone
occupies. -/
theorem getUInt16?_putUInt16s_alone (l : List UInt16) (i : Nat) (h : i < l.length) :
    Protocol.getUInt16? (putUInt16s l) (2 * i) = some l[i] := by
  have := getUInt16?_putUInt16s_prefix l ByteArray.empty i h
  rwa [ByteArray.append_empty] at this

/-- A 16-bit wire field written from a `Nat` below `2^15` reads back as that
`Nat` through the wire's signed interpretation. -/
theorem toInt16_toInt_ofNat {k : Nat} (h : k < 32768) :
    (UInt16.ofNat k).toInt16.toInt = (k : Int) := by
  rw [show (UInt16.ofNat k) = (Int16.ofNat k).toUInt16 from rfl, Int16.toInt16_toUInt16]
  exact Int16.toInt_ofNat_of_lt h

/-- **Binary `numeric` roundtrips losslessly.** Every field of a finite
`numeric` — sign, weight, display scale, and each base-10000 digit — is
recovered exactly. The hypotheses are the wire's own limits: the three header
counts are `int16` fields and PostgreSQL's digits are below 10000. -/
theorem PgNumeric.fromBinary_toBinary {neg : Bool} {digits : Array UInt16}
    {weight : Int} {dscale : Nat}
    (hcount : digits.size < 32768)
    (hweightLo : -32768 ≤ weight) (hweightHi : weight < 32768)
    (hscale : dscale < 32768)
    (hdigits : ∀ d ∈ digits, d < 10000) :
    PgNumeric.fromBinary (PgNumeric.toBinary ⟨neg, digits, weight, dscale, none⟩) =
      .ok ⟨neg, digits, weight, dscale, none⟩ := by
  have hbin : PgNumeric.toBinary ⟨neg, digits, weight, dscale, none⟩ =
      putUInt16s [UInt16.ofNat digits.size, (Int16.ofInt weight).toUInt16,
        (if neg then 0x4000 else 0), UInt16.ofNat dscale] ++ putUInt16s digits.toList := by
    show putUInt16s ([UInt16.ofNat digits.size, (Int16.ofInt weight).toUInt16,
      (if neg then 0x4000 else 0), UInt16.ofNat dscale] ++ digits.toList) = _
    exact putUInt16s_append _ _
  -- The four header words read back.
  have h0 : Protocol.getUInt16? (PgNumeric.toBinary ⟨neg, digits, weight, dscale, none⟩) 0
      = some (UInt16.ofNat digits.size) := by
    rw [hbin]; simpa using getUInt16?_putUInt16s_prefix _ _ 0 (by simp)
  have h2 : Protocol.getUInt16? (PgNumeric.toBinary ⟨neg, digits, weight, dscale, none⟩) 2
      = some (Int16.ofInt weight).toUInt16 := by
    rw [hbin]; simpa using getUInt16?_putUInt16s_prefix _ _ 1 (by simp)
  have h4 : Protocol.getUInt16? (PgNumeric.toBinary ⟨neg, digits, weight, dscale, none⟩) 4
      = some (if neg then 0x4000 else 0) := by
    rw [hbin]; simpa using getUInt16?_putUInt16s_prefix _ _ 2 (by simp)
  have h6 : Protocol.getUInt16? (PgNumeric.toBinary ⟨neg, digits, weight, dscale, none⟩) 6
      = some (UInt16.ofNat dscale) := by
    rw [hbin]; simpa using getUInt16?_putUInt16s_prefix _ _ 3 (by simp)
  -- The digits read back.
  have hdig : readNumericDigits (PgNumeric.toBinary ⟨neg, digits, weight, dscale, none⟩) 8
      digits.size #[] = .ok digits := by
    have hpre := readNumericDigits_putUInt16s digits.toList
      (putUInt16s [UInt16.ofNat digits.size, (Int16.ofInt weight).toUInt16,
        (if neg then 0x4000 else 0), UInt16.ofNat dscale]) #[]
      (fun d hd => hdigits d (by simpa using hd))
    rw [show (putUInt16s [UInt16.ofNat digits.size, (Int16.ofInt weight).toUInt16,
        (if neg then 0x4000 else 0), UInt16.ofNat dscale]).size = 8 from by
      rw [size_putUInt16s]; rfl] at hpre
    rw [← hbin, Array.length_toList] at hpre
    simpa using hpre
  -- Header fields decode to the values they were built from.
  have hcnt : (UInt16.ofNat digits.size).toInt16.toInt.toNat = digits.size := by
    rw [toInt16_toInt_ofNat hcount]; exact Int.toNat_natCast _
  have hwt : ((Int16.ofInt weight).toUInt16).toInt16.toInt = weight := by
    rw [Int16.toInt16_toUInt16]; exact Int16.toInt_ofInt_of_le hweightLo hweightHi
  have hsc : (UInt16.ofNat dscale).toInt16.toInt.toNat = dscale := by
    rw [toInt16_toInt_ofNat hscale]; exact Int.toNat_natCast _
  unfold PgNumeric.fromBinary
  rw [h0, h2, h4, h6]
  cases neg with
  | false =>
    rw [if_neg (by decide : ¬((false : Bool) = true))]
    show (if (0 : UInt16).toNat == 0 || (0 : UInt16).toNat == 0x4000 then
      match readNumericDigits _ 8 (UInt16.ofNat digits.size).toInt16.toInt.toNat #[] with
      | .ok ds => Except.ok (PgNumeric.mk ((0 : UInt16).toNat == 0x4000) ds
          ((Int16.ofInt weight).toUInt16.toInt16.toInt)
          ((UInt16.ofNat dscale).toInt16.toInt.toNat) none)
      | .error e => .error e
    else .error s!"bad numeric sign {(0 : UInt16).toNat}") = _
    rw [if_pos (by decide), hcnt, hdig, hwt, hsc]
    rfl
  | true =>
    rw [if_pos rfl]
    show (if (0x4000 : UInt16).toNat == 0 || (0x4000 : UInt16).toNat == 0x4000 then
      match readNumericDigits _ 8 (UInt16.ofNat digits.size).toInt16.toInt.toNat #[] with
      | .ok ds => Except.ok (PgNumeric.mk ((0x4000 : UInt16).toNat == 0x4000) ds
          ((Int16.ofInt weight).toUInt16.toInt16.toInt)
          ((UInt16.ofNat dscale).toInt16.toInt.toNat) none)
      | .error e => .error e
    else .error s!"bad numeric sign {(0x4000 : UInt16).toNat}") = _
    rw [if_pos (by decide), hcnt, hdig, hwt, hsc]
    rfl

/-- Reading a written four-word header back, word by word. -/
theorem getUInt16?_putUInt16s4 (a b c d : UInt16) :
    Protocol.getUInt16? (putUInt16s [a, b, c, d]) 0 = some a ∧
    Protocol.getUInt16? (putUInt16s [a, b, c, d]) 2 = some b ∧
    Protocol.getUInt16? (putUInt16s [a, b, c, d]) 4 = some c ∧
    Protocol.getUInt16? (putUInt16s [a, b, c, d]) 6 = some d := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa using getUInt16?_putUInt16s_alone [a, b, c, d] 0 (by simp)
  · simpa using getUInt16?_putUInt16s_alone [a, b, c, d] 1 (by simp)
  · simpa using getUInt16?_putUInt16s_alone [a, b, c, d] 2 (by simp)
  · simpa using getUInt16?_putUInt16s_alone [a, b, c, d] 3 (by simp)

/-- The three special values roundtrip too: their sentinel signs are exactly
the ones `fromBinary` recognizes. -/
theorem PgNumeric.fromBinary_toBinary_special (sp : PgNumeric.Special) :
    PgNumeric.fromBinary (PgNumeric.toBinary { special := some sp }) =
      .ok { special := some sp } := by
  have h := getUInt16?_putUInt16s4 0 0 (PgNumeric.specialSign sp) 0
  show PgNumeric.fromBinary (putUInt16s [0, 0, PgNumeric.specialSign sp, 0]) = _
  unfold PgNumeric.fromBinary
  rw [h.1, h.2.1, h.2.2.1, h.2.2.2]
  cases sp <;> rfl


/-!
### `interval`: the text roundtrip

`PgInterval.toString` renders the default `postgres` interval style and
`fromString` parses it. The law below says the two invert each other for
*every* interval — months, days and microseconds, sign and sub-second
fraction included. Unlike `numeric`, no side condition is needed: the three
components are independent, so nothing can be lost.

The proof walks the rendering: the token list is joined with single spaces and
re-split (`splitOn_joinSpace`), trimming is the identity because no token
starts or ends with whitespace (`trim_joinSpace`), and then one `step_*` lemma
per token kind drives the parser's state machine.
-/

namespace PgInterval

private theorem splitOn_three {A B C : List Char}
    (hA : ':' ∉ A) (hB : ':' ∉ B) (hC : ':' ∉ C) :
    (A ++ ':' :: (B ++ ':' :: C)).splitOn ':' = [A, B, C] := by
  rw [List.splitOn_append_cons_self_of_not_mem hA,
    List.splitOn_append_cons_self_of_not_mem hB, List.splitOn_eq_singleton hC]

private theorem splitOn_two {P Q : List Char} (hP : '.' ∉ P) (hQ : '.' ∉ Q) :
    (P ++ '.' :: Q).splitOn '.' = [P, Q] := by
  rw [List.splitOn_append_cons_self_of_not_mem hP, List.splitOn_eq_singleton hQ]

private theorem not_mem_hmsChars {sep : Char} (hsep : isAsciiDigit sep = false)
    (hne : sep ≠ ':') (us : Nat) : sep ∉ hmsChars us := by
  unfold hmsChars
  simp only [List.mem_append, List.mem_cons, not_or]
  exact ⟨not_mem_padDigits hsep, hne, not_mem_padDigits hsep, hne,
    not_mem_padDigits hsep⟩

private theorem colon_not_mem_padDigits (w n : Nat) : ':' ∉ padDigits w n :=
  not_mem_padDigits (by decide)

theorem fracMicros_padDigits {f : Nat} (hf : f < 1000000) :
    fracMicros (padDigits 6 f) = some f := by
  have hlen : (padDigits 6 f).length = 6 :=
    padDigits_length (natDigits_length_le 5 f (by omega))
  unfold fracMicros
  rw [List.take_left' hlen, natOfDigitsFull_padDigits]

theorem hmsMicros_hmsChars (orig : String) (us f : Nat) :
    hmsMicros orig (hmsChars us) f =
      .ok (Int.ofNat ((us / 3600000000 * 3600 + us / 60000000 % 60 * 60 +
        us / 1000000 % 60) * 1000000 + f)) := by
  unfold hmsMicros hmsChars
  rw [splitOn_three (colon_not_mem_padDigits 2 _) (colon_not_mem_padDigits 2 _)
    (colon_not_mem_padDigits 2 _)]
  simp only [natOfDigitsFull_padDigits]

theorem timeMagnitude_timeBody (orig : String) (us : Nat) :
    timeMagnitude orig (timeBody us) = .ok (Int.ofNat us) := by
  unfold timeMagnitude timeBody
  by_cases hf : us % 1000000 = 0
  · rw [if_pos hf, List.append_nil,
      List.splitOn_eq_singleton (not_mem_hmsChars (by decide) (by decide) us)]
    show hmsMicros orig (hmsChars us) 0 = _
    rw [hmsMicros_hmsChars]
    congr 1
    exact congrArg Int.ofNat (by omega)
  · rw [if_neg hf, splitOn_two (not_mem_hmsChars (by decide) (by decide) us)
      (not_mem_padDigits (by decide))]
    show (match fracMicros (padDigits 6 (us % 1000000)) with
      | some v => hmsMicros orig (hmsChars us) v
      | none => .error s!"interval: bad fraction {orig}") = _
    rw [fracMicros_padDigits (Nat.mod_lt _ (by omega))]
    show hmsMicros orig (hmsChars us) (us % 1000000) = _
    rw [hmsMicros_hmsChars]
    congr 1
    exact congrArg Int.ofNat (by omega)

private theorem not_mem_timeChars {sep : Char} (h1 : isAsciiDigit sep = false)
    (h2 : sep ≠ ':') (h3 : sep ≠ '.') (h4 : sep ≠ '-') (v : Int) :
    sep ∉ timeChars v := by
  unfold timeChars timeBody
  simp only [List.mem_append, not_or]
  refine ⟨?_, not_mem_hmsChars h1 h2 v.natAbs, ?_⟩
  · split
    · simp only [List.mem_cons, List.not_mem_nil, or_false]; exact h4
    · exact List.not_mem_nil
  · split
    · exact List.not_mem_nil
    · simp only [List.mem_cons, not_or]
      exact ⟨h3, not_mem_padDigits h1⟩

private theorem colon_mem_timeChars (v : Int) : ':' ∈ timeChars v := by
  unfold timeChars timeBody hmsChars
  simp

private theorem not_mem_intChars {sep : Char} (h1 : isAsciiDigit sep = false)
    (h4 : sep ≠ '-') (v : Int) : sep ∉ intChars v := by
  unfold intChars
  split
  · simp only [List.mem_cons, not_or]
    exact ⟨h4, not_mem_natDigits h1⟩
  · exact not_mem_natDigits h1

private theorem joinSpace_cons {p : List Char} {ts : List (List Char)} (h : ts ≠ []) :
    joinSpace (p :: ts) = p ++ ' ' :: joinSpace ts := by
  cases ts with
  | nil => exact absurd rfl h
  | cons u us => rfl

private theorem joinSpace_ne_nil : ∀ {ts : List (List Char)}, ts ≠ [] →
    (∀ t ∈ ts, t ≠ []) → joinSpace ts ≠ [] := by
  intro ts hne hall
  cases ts with
  | nil => exact absurd rfl hne
  | cons t rest =>
    cases rest with
    | nil => exact hall t (List.mem_cons_self ..)
    | cons u us =>
      rw [joinSpace_cons (List.cons_ne_nil _ _)]
      exact List.append_ne_nil_of_right_ne_nil _ (List.cons_ne_nil _ _)

private theorem head?_joinSpace_mem : ∀ (ts : List (List Char)) (c : Char),
    (∀ t ∈ ts, t ≠ []) → (joinSpace ts).head? = some c → ∃ t, t ∈ ts ∧ c ∈ t := by
  intro ts c hall hhd
  cases ts with
  | nil => exact absurd hhd (by simp [joinSpace])
  | cons t rest =>
    refine ⟨t, List.mem_cons_self .., ?_⟩
    cases rest with
    | nil => exact List.mem_of_mem_head? (by rw [show joinSpace [t] = t from rfl] at hhd; exact hhd)
    | cons u us =>
      rw [joinSpace_cons (List.cons_ne_nil _ _), List.head?_append] at hhd
      cases ht : t with
      | nil => exact absurd ht (hall t (List.mem_cons_self ..))
      | cons a b =>
        rw [ht] at hhd
        simp only [List.head?_cons, Option.some_or, Option.some.injEq] at hhd
        subst hhd
        exact List.mem_cons_self ..

private theorem getLast?_joinSpace_mem : ∀ (ts : List (List Char)) (c : Char),
    (∀ t ∈ ts, t ≠ []) → (joinSpace ts).getLast? = some c → ∃ t, t ∈ ts ∧ c ∈ t := by
  intro ts
  induction ts with
  | nil => intro c _ hl; exact absurd hl (by simp [joinSpace])
  | cons t rest ih =>
    intro c hall hl
    cases rest with
    | nil =>
      exact ⟨t, List.mem_cons_self ..,
        List.mem_of_getLast? (by rwa [show joinSpace [t] = t from rfl] at hl)⟩
    | cons u us =>
      rw [joinSpace_cons (List.cons_ne_nil _ _),
        show (' ' :: joinSpace (u :: us)) = [' '] ++ joinSpace (u :: us) from rfl,
        ← List.append_assoc, List.getLast?_append] at hl
      have hX : joinSpace (u :: us) ≠ [] :=
        joinSpace_ne_nil (List.cons_ne_nil _ _) (fun x hx => hall x (List.mem_cons_of_mem _ hx))
      cases hg : (joinSpace (u :: us)).getLast? with
      | none => exact absurd (List.getLast?_eq_none_iff.mp hg) hX
      | some z =>
        rw [hg, Option.some_or, Option.some.injEq] at hl
        subst hl
        obtain ⟨t', ht', hc⟩ :=
          ih z (fun x hx => hall x (List.mem_cons_of_mem _ hx)) hg
        exact ⟨t', List.mem_cons_of_mem _ ht', hc⟩

private theorem trim_joinSpace {ts : List (List Char)} (hne : ∀ t ∈ ts, t ≠ [])
    (hsp : ∀ t ∈ ts, ∀ c ∈ t, isAsciiSpace c = false) :
    trimAsciiChars (joinSpace ts) = joinSpace ts := by
  refine trimAsciiChars_eq_self (fun c hc => ?_) (fun c hc => ?_)
  · obtain ⟨t, ht, hct⟩ := head?_joinSpace_mem ts c hne hc
    exact hsp t ht c hct
  · obtain ⟨t, ht, hct⟩ := getLast?_joinSpace_mem ts c hne hc
    exact hsp t ht c hct

private theorem splitOn_joinSpace : ∀ (ts : List (List Char)), ts ≠ [] →
    (∀ t ∈ ts, ' ' ∉ t) → (joinSpace ts).splitOn ' ' = ts := by
  intro ts
  induction ts with
  | nil => intro h; exact absurd rfl h
  | cons t rest ih =>
    intro _ hall
    cases rest with
    | nil =>
      rw [show joinSpace [t] = t from rfl,
        List.splitOn_eq_singleton (hall t (List.mem_cons_self ..))]
    | cons u us =>
      rw [joinSpace_cons (List.cons_ne_nil _ _),
        List.splitOn_append_cons_self_of_not_mem (hall t (List.mem_cons_self ..)),
        ih (List.cons_ne_nil _ _) (fun x hx => hall x (List.mem_cons_of_mem _ hx))]

private theorem not_mem_timeBody {sep : Char} (h1 : isAsciiDigit sep = false)
    (h2 : sep ≠ ':') (h3 : sep ≠ '.') (us : Nat) : sep ∉ timeBody us := by
  unfold timeBody
  simp only [List.mem_append, not_or]
  refine ⟨not_mem_hmsChars h1 h2 us, ?_⟩
  split
  · exact List.not_mem_nil
  · simp only [List.mem_cons, not_or]
    exact ⟨h3, not_mem_padDigits h1⟩

private theorem timeBody_ne_nil (us : Nat) : timeBody us ≠ [] := by
  unfold timeBody hmsChars
  cases hp : padDigits 2 (us / 3600000000) with
  | nil => exact absurd hp (padDigits_ne_nil 2 _)
  | cons c t => simp

private theorem intChars_ne_nil (v : Int) : intChars v ≠ [] := by
  unfold intChars
  split
  · exact List.cons_ne_nil _ _
  · exact natDigits_ne_nil _

private theorem timeChars_ne_nil (v : Int) : timeChars v ≠ [] := by
  unfold timeChars
  exact List.append_ne_nil_of_right_ne_nil _ (timeBody_ne_nil _)

theorem intOfChars_intChars (v : Int) : intOfChars (intChars v) = some v := by
  unfold intChars
  by_cases hv : v < 0
  · rw [if_pos hv]
    simp only [intOfChars, beq_self_eq_true, if_true, natOfDigitsFull_natDigits,
      Option.map_some, Option.some.injEq, Int.ofNat_eq_natCast]
    omega
  · rw [if_neg hv]
    cases hn : natDigits v.natAbs with
    | nil => exact absurd hn (natDigits_ne_nil _)
    | cons a b =>
      have hne : a ≠ '-' := by
        intro h
        exact absurd (show ('-' : Char) ∈ natDigits v.natAbs by
          rw [hn, ← h]; exact List.mem_cons_self ..) (not_mem_natDigits (by decide))
      simp only [intOfChars, beq_false_of_ne hne]
      rw [← hn, natOfDigitsFull_natDigits, Option.map_some]
      exact congrArg some (by simp only [Int.ofNat_eq_natCast]; omega)

theorem parseTime_timeChars (orig : String) (v : Int) :
    parseTime orig (timeChars v) = .ok v := by
  unfold timeChars
  by_cases hv : v < 0
  · rw [if_pos hv]
    simp only [List.cons_append, List.nil_append, parseTime, beq_self_eq_true, if_true,
      timeMagnitude_timeBody, Except.map, Except.ok.injEq, Int.ofNat_eq_natCast]
    omega
  · rw [if_neg hv, List.nil_append]
    cases hb : timeBody v.natAbs with
    | nil => exact absurd hb (timeBody_ne_nil _)
    | cons a b =>
      have hmem : a ∈ timeBody v.natAbs := by rw [hb]; exact List.mem_cons_self ..
      have hminus : a ≠ '-' := by
        intro h; exact absurd (h ▸ hmem) (not_mem_timeBody (by decide) (by decide) (by decide) _)
      have hplus : a ≠ '+' := by
        intro h; exact absurd (h ▸ hmem) (not_mem_timeBody (by decide) (by decide) (by decide) _)
      simp only [parseTime, beq_false_of_ne hminus, beq_false_of_ne hplus]
      rw [← hb, timeMagnitude_timeBody]
      exact congrArg Except.ok (by simp only [Int.ofNat_eq_natCast]; omega)

private theorem contains_false_of_not_mem {l : List Char} {c : Char} (h : c ∉ l) :
    l.contains c = false := by
  cases hc : l.contains c with
  | false => rfl
  | true => exact absurd (List.contains_iff_mem.mp hc) h

private theorem step_nil (orig : String) (iv : PgInterval) : step orig iv none [] = .ok iv := rfl

private theorem step_num (orig : String) (iv : PgInterval) (v : Int)
    (rest : List (List Char)) :
    step orig iv none (intChars v :: rest) = step orig iv (some v) rest := by
  simp only [step,
    contains_false_of_not_mem (not_mem_intChars (sep := ':') (by decide) (by decide) v),
    Bool.false_eq_true, if_false, intOfChars_intChars]

private theorem step_mons (orig : String) (iv : PgInterval) (n : Int)
    (rest : List (List Char)) :
    step orig iv (some n) (['m', 'o', 'n', 's'] :: rest) =
      step orig { iv with months := iv.months + n } none rest := rfl

private theorem step_days (orig : String) (iv : PgInterval) (n : Int)
    (rest : List (List Char)) :
    step orig iv (some n) (['d', 'a', 'y', 's'] :: rest) =
      step orig { iv with days := iv.days + n } none rest := rfl

private theorem step_time (orig : String) (iv : PgInterval) (v : Int) :
    step orig iv none [timeChars v] = .ok { iv with micros := iv.micros + v } := by
  simp only [step, List.contains_iff_mem, colon_mem_timeChars, if_true,
    Option.isNone_none, parseTime_timeChars]

private theorem mem_tokens (iv : PgInterval) : ∀ t ∈ iv.tokens,
    (∃ v : Int, t = intChars v) ∨ t = ['m', 'o', 'n', 's'] ∨ t = ['d', 'a', 'y', 's'] ∨
      (∃ v : Int, t = timeChars v) := by
  intro t ht
  unfold tokens at ht
  simp only [List.mem_append] at ht
  rcases ht with (ht | ht) | ht
  · split at ht
    · exact absurd ht List.not_mem_nil
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl
      · exact Or.inl ⟨_, rfl⟩
      · exact Or.inr (Or.inl rfl)
  · split at ht
    · exact absurd ht List.not_mem_nil
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl
      · exact Or.inl ⟨_, rfl⟩
      · exact Or.inr (Or.inr (Or.inl rfl))
  · split at ht
    · exact absurd ht List.not_mem_nil
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
      exact Or.inr (Or.inr (Or.inr ⟨_, ht⟩))

private theorem tokens_ne_nil (iv : PgInterval) : ∀ t ∈ iv.tokens, t ≠ [] := by
  intro t ht
  rcases mem_tokens iv t ht with ⟨v, rfl⟩ | rfl | rfl | ⟨v, rfl⟩
  · exact intChars_ne_nil v
  · exact List.cons_ne_nil _ _
  · exact List.cons_ne_nil _ _
  · exact timeChars_ne_nil v

private theorem space_not_digit {c : Char} (h : isAsciiSpace c = true) :
    isAsciiDigit c = false ∧ c ≠ ':' ∧ c ≠ '.' ∧ c ≠ '-' := by
  simp only [isAsciiSpace, Bool.or_eq_true, beq_iff_eq] at h
  rcases h with ((rfl | rfl) | rfl) | rfl <;>
    exact ⟨by decide, by decide, by decide, by decide⟩

private theorem tokens_space_free (iv : PgInterval) :
    ∀ t ∈ iv.tokens, ∀ c ∈ t, isAsciiSpace c = false := by
  intro t ht c hc
  cases hsp' : isAsciiSpace c with
  | false => rfl
  | true =>
  exfalso
  obtain ⟨h1, h2, h3, h4⟩ := space_not_digit hsp'
  rcases mem_tokens iv t ht with ⟨v, rfl⟩ | rfl | rfl | ⟨v, rfl⟩
  · exact not_mem_intChars h1 h4 v hc
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl <;> exact absurd hsp' (by decide)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl <;> exact absurd hsp' (by decide)
  · exact not_mem_timeChars h1 h2 h3 h4 v hc

private theorem tokens_list_ne_nil (iv : PgInterval) : iv.tokens ≠ [] := by
  unfold tokens
  by_cases hm : iv.months = 0
  · by_cases hd : iv.days = 0
    · rw [if_pos hm, if_pos hd, if_neg (by simp [hm, hd])]
      simp
    · rw [if_pos hm, if_neg hd]
      simp
  · rw [if_neg hm]
    simp

-- One uniform rewrite set for all eight shapes of the token list; which of the
-- `step_*` lemmas fires depends on the case, so some are unused in each.
set_option linter.unusedSimpArgs false in
private theorem step_tokens (orig : String) (iv : PgInterval) :
    step orig {} none iv.tokens = .ok iv := by
  obtain ⟨mo, dy, us⟩ := iv
  unfold tokens
  by_cases hm : mo = 0 <;> by_cases hd : dy = 0 <;> by_cases hu : us = 0
  · rw [if_pos hm, if_pos hd, if_neg (by simp [hm, hd])]
    simp only [List.nil_append, List.append_nil, List.cons_append, step_num,
      step_mons, step_days, step_time, step_nil]
    simp [hm, hd, hu]
  · rw [if_pos hm, if_pos hd, if_neg (by simp [hm, hd])]
    simp only [List.nil_append, List.append_nil, List.cons_append, step_num,
      step_mons, step_days, step_time, step_nil]
    simp [hm, hd, hu]
  · rw [if_pos hm, if_neg hd, if_pos (by exact ⟨hu, by simp [hd]⟩)]
    simp only [List.nil_append, List.append_nil, List.cons_append, step_num,
      step_mons, step_days, step_time, step_nil]
    simp [hm, hd, hu]
  · rw [if_pos hm, if_neg hd, if_neg (by simp [hu])]
    simp only [List.nil_append, List.append_nil, List.cons_append, step_num,
      step_mons, step_days, step_time, step_nil]
    simp [hm, hd, hu]
  · rw [if_neg hm, if_pos hd, if_pos (by exact ⟨hu, by simp [hm]⟩)]
    simp only [List.nil_append, List.append_nil, List.cons_append, step_num,
      step_mons, step_days, step_time, step_nil]
    simp [hm, hd, hu]
  · rw [if_neg hm, if_pos hd, if_neg (by simp [hu])]
    simp only [List.nil_append, List.append_nil, List.cons_append, step_num,
      step_mons, step_days, step_time, step_nil]
    simp [hm, hd, hu]
  · rw [if_neg hm, if_neg hd, if_pos (by exact ⟨hu, by simp [hm]⟩)]
    simp only [List.nil_append, List.append_nil, List.cons_append, step_num,
      step_mons, step_days, step_time, step_nil]
    simp [hm, hd, hu]
  · rw [if_neg hm, if_neg hd, if_neg (by simp [hu])]
    simp only [List.nil_append, List.append_nil, List.cons_append, step_num,
      step_mons, step_days, step_time, step_nil]
    simp [hm, hd, hu]

/-- **An interval renders and parses back to itself**, unconditionally: the
month, day and microsecond components are recovered exactly, sign and
sub-second fraction included. -/
theorem fromString_toString (iv : PgInterval) : fromString iv.toString = .ok iv := by
  have hne := tokens_ne_nil iv
  have hsp := tokens_space_free iv
  unfold fromString
  rw [toString_eq, String.toList_ofList, trim_joinSpace hne hsp,
    splitOn_joinSpace _ (tokens_list_ne_nil iv)
      (fun t ht hmem => absurd (hsp t ht ' ' hmem) (by decide)),
    List.filter_eq_self.mpr (fun t ht => by
      cases t with
      | nil => exact absurd rfl (hne [] ht)
      | cons _ _ => rfl),
    step_tokens]

end PgInterval


/-!
### `numeric`: the text roundtrip

The binary form is already proved lossless (`PgNumeric.fromBinary_toBinary`);
this is the same statement for the text form, which is what a `numeric`
parameter and a text-format result column actually travel as.

The argument is one chain: the rendered digit string, once the parser has
padded the integer part on the left and the fraction on the right to whole
base-10000 groups, is *exactly* `flatMap digits4` of the value's own group
list (`chars_groups`); regrouping it four characters at a time therefore
returns those groups unchanged (`group4_flatMap`, the lemma that says no
precision is lost); the group list is the digits array flanked by the zero
groups the padding introduced (`groups_shape`); and stripping those zero
groups restores the digits and the weight.

`Canonical` states what has to hold for that to be a roundtrip rather than a
truncation: digits in base-10000 range, no leading or trailing zero group,
zero spelled canonically, and a display scale wide enough to reach the last
digit. PostgreSQL's own `numeric` values satisfy it — the example at the end
of this section is `12345.678` exactly as the server sends it.
-/

namespace PgNumeric

-- ── digit-group primitives ────────────────────────────────────────────────

private theorem digitChar_zero : digitChar 0 = '0' := by decide

private theorem digitChar_mod (v : Nat) : digitChar (v % 10) = digitChar v := by
  unfold digitChar
  congr 1
  omega

private theorem natDigits_lt (v : Nat) (h : v < 10) : natDigits v = [digitChar v] := by
  rw [natDigits, if_pos h]

private theorem natDigits_ge (v : Nat) (h : ¬ v < 10) :
    natDigits v = natDigits (v / 10) ++ [digitChar v] := by
  rw [natDigits, if_neg h, digitChar_mod]

theorem digits4_eq_padDigits {v : Nat} (h : v < 10000) : digits4 v = padDigits 4 v := by
  unfold digits4 padDigits
  by_cases h1 : v < 10
  · rw [natDigits_lt v h1]
    simp only [List.length_cons, List.length_nil]
    rw [show v / 1000 = 0 from by omega, show v / 100 = 0 from by omega,
      show v / 10 = 0 from by omega, digitChar_zero]
    rfl
  · rw [natDigits_ge v h1]
    by_cases h2 : v / 10 < 10
    · rw [natDigits_lt _ h2]
      simp only [List.length_append, List.length_cons, List.length_nil]
      rw [show v / 1000 = 0 from by omega, show v / 100 = 0 from by omega,
        digitChar_zero]
      rfl
    · rw [natDigits_ge _ h2, show v / 10 / 10 = v / 100 from by omega]
      by_cases h3 : v / 100 < 10
      · rw [natDigits_lt _ h3]
        simp only [List.length_append, List.length_cons, List.length_nil]
        rw [show v / 1000 = 0 from by omega, digitChar_zero]
        rfl
      · rw [natDigits_ge _ h3, show v / 100 / 10 = v / 1000 from by omega,
          natDigits_lt _ (by omega)]
        simp only [List.length_append, List.length_cons, List.length_nil]
        rfl

private theorem length_digits4 (v : Nat) : (digits4 v).length = 4 := rfl

private theorem natOfDigits_digits4 {v : Nat} (h : v < 10000) :
    (natOfDigits 0 (digits4 v)).getD 0 = v := by
  rw [digits4_eq_padDigits h, natOfDigits_padDigits]
  rfl

/-- Regrouping a rendered digit string recovers exactly the groups it came
from. This is the lemma that says no precision is lost. -/
theorem group4_flatMap : ∀ (ds : List Nat), (∀ d ∈ ds, d < 10000) →
    ∀ out : Array UInt16,
    group4 (ds.flatMap digits4) out = out ++ (ds.map UInt16.ofNat).toArray := by
  intro ds
  induction ds with
  | nil => intro _ out; simp [group4]
  | cons v t ih =>
    intro hall out
    have hv : v < 10000 := hall v (List.mem_cons_self ..)
    simp only [List.flatMap_cons, digits4, List.cons_append, group4,
      List.nil_append, List.map_cons]
    rw [show (natOfDigits 0 [digitChar (v / 1000), digitChar (v / 100), digitChar (v / 10),
        digitChar v]).getD 0 = v from natOfDigits_digits4 hv,
      ih (fun d hd => hall d (List.mem_cons_of_mem _ hd))]
    simp



-- ── the group list ────────────────────────────────────────────────────────

private theorem digitAt_neg {n : PgNumeric} {i : Int} (h : i < 0) : n.digitAt i = 0 := by
  unfold digitAt; rw [if_pos h]

private theorem digitAt_ge {n : PgNumeric} {i : Int} (h : (n.digits.size : Int) ≤ i) :
    n.digitAt i = 0 := by
  unfold digitAt
  by_cases hn : i < 0
  · rw [if_pos hn]
  · rw [if_neg hn, Array.getElem?_eq_none (by omega)]
    rfl

private theorem digitAt_lt {n : PgNumeric} {s : Nat} (h : s < n.digits.size) :
    n.digitAt (s : Int) = (n.digits[s]'h).toNat := by
  unfold digitAt
  rw [if_neg (by omega), Array.getElem?_eq_getElem (by omega)]
  rfl

theorem groupList_length {n : PgNumeric} : ∀ (k : Nat) (s : Int),
    (n.groupList s k).length = k := by
  intro k
  induction k with
  | zero => intro s; rfl
  | succ j ih => intro s; simp only [groupList, List.length_cons, ih]

theorem groupList_append {n : PgNumeric} : ∀ (a b : Nat) (s : Int),
    n.groupList s (a + b) = n.groupList s a ++ n.groupList (s + (a : Int)) b := by
  intro a
  induction a with
  | zero => intro b s; simp [groupList]
  | succ j ih =>
    intro b s
    have hidx : s + ((j + 1 : Nat) : Int) = (s + 1) + (j : Int) := by omega
    rw [show j + 1 + b = (j + b) + 1 from by omega]
    show n.digitAt s :: n.groupList (s + 1) (j + b) = _
    rw [ih b (s + 1), hidx]
    show _ = (n.digitAt s :: n.groupList (s + 1) j) ++ _
    rw [List.cons_append]

theorem groupList_zeros {n : PgNumeric} : ∀ (k : Nat) (s : Int), s + (k : Int) ≤ 0 →
    n.groupList s k = List.replicate k 0 := by
  intro k
  induction k with
  | zero => intro s _; rfl
  | succ j ih =>
    intro s hs
    show n.digitAt s :: n.groupList (s + 1) j = _
    rw [digitAt_neg (by omega), ih (s + 1) (by omega), List.replicate_succ]

theorem groupList_zeros_right {n : PgNumeric} : ∀ (k : Nat) (s : Int),
    (n.digits.size : Int) ≤ s → n.groupList s k = List.replicate k 0 := by
  intro k
  induction k with
  | zero => intro s _; rfl
  | succ j ih =>
    intro s hs
    show n.digitAt s :: n.groupList (s + 1) j = _
    rw [digitAt_ge hs, ih (s + 1) (by omega), List.replicate_succ]

theorem groupList_digits {n : PgNumeric} : ∀ (k s : Nat), s + k ≤ n.digits.size →
    (n.groupList (s : Int) k).map UInt16.ofNat = (n.digits.toList.drop s).take k := by
  intro k
  induction k with
  | zero => intro s _; simp [groupList]
  | succ j ih =>
    intro s hs
    have hlt : s < n.digits.size := by omega
    show (UInt16.ofNat (n.digitAt (s : Int)) :: _) = _
    rw [digitAt_lt hlt, UInt16.ofNat_toNat,
      show ((s : Int) + 1) = ((s + 1 : Nat) : Int) from by omega,
      ih (s + 1) (by omega)]
    rw [show n.digits.toList.drop s
        = n.digits.toList[s]'(by simp only [Array.length_toList]; omega)
          :: n.digits.toList.drop (s + 1) from
      List.drop_eq_getElem_cons (by simp only [Array.length_toList]; omega)]
    simp

theorem groupList_lt {n : PgNumeric} (hall : ∀ i, n.digitAt i < 10000) :
    ∀ (k : Nat) (s : Int), ∀ d ∈ n.groupList s k, d < 10000 := by
  intro k
  induction k with
  | zero => intro s d hd; exact absurd hd List.not_mem_nil
  | succ j ih =>
    intro s d hd
    rcases List.mem_cons.mp hd with rfl | hd
    · exact hall s
    · exact ih (s + 1) d hd

theorem length_flatMap_digits4 : ∀ (l : List Nat),
    (l.flatMap digits4).length = 4 * l.length := by
  intro l
  induction l with
  | nil => rfl
  | cons v t ih =>
    simp only [List.flatMap_cons, List.length_append, ih, length_digits4, List.length_cons]
    omega



-- ── the rendered digit string is exactly the group list, regrouped ────────

private theorem digitChar_eq_zero {x : Nat} (h : x % 10 = 0) : digitChar x = '0' := by
  unfold digitChar
  rw [h]

private theorem flatMap_padDigits_eq : ∀ (l : List Nat), (∀ d ∈ l, d < 10000) →
    l.flatMap (padDigits 4) = l.flatMap digits4 := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons v t ih =>
    intro hall
    simp only [List.flatMap_cons, digits4_eq_padDigits (hall v (List.mem_cons_self ..)),
      ih (fun d hd => hall d (List.mem_cons_of_mem _ hd))]

private theorem groupList_snoc {n : PgNumeric} (q : Nat) (s : Int) :
    n.groupList s (q + 1) = n.groupList s q ++ [n.digitAt (s + (q : Int))] :=
  groupList_append q 1 s

theorem alignInt_intChars {n : PgNumeric} (hall : ∀ i, n.digitAt i < 10000) :
    alignInt n.intChars = (n.groupList n.baseIndex (n.intGroups + 1)).flatMap digits4 := by
  have hL1 : 1 ≤ (natDigits (n.digitAt n.baseIndex)).length :=
    List.length_pos_iff.mpr (natDigits_ne_nil _)
  have hL4 : (natDigits (n.digitAt n.baseIndex)).length ≤ 4 :=
    natDigits_length_le 3 _ (by have := hall n.baseIndex; omega)
  have hflat : (n.groupList (n.baseIndex + 1) n.intGroups).flatMap (padDigits 4) =
      (n.groupList (n.baseIndex + 1) n.intGroups).flatMap digits4 :=
    flatMap_padDigits_eq _ (groupList_lt hall _ _)
  have hlen : ((n.groupList (n.baseIndex + 1) n.intGroups).flatMap digits4).length
      = 4 * n.intGroups := by
    rw [length_flatMap_digits4, groupList_length]
  show List.replicate ((4 - n.intChars.length % 4) % 4) '0' ++ n.intChars = _
  unfold intChars
  rw [hflat]
  rw [show ((4 : Nat) - (natDigits (n.digitAt n.baseIndex) ++
      (n.groupList (n.baseIndex + 1) n.intGroups).flatMap digits4).length % 4) % 4
      = 4 - (natDigits (n.digitAt n.baseIndex)).length from by
    rw [List.length_append, hlen]; omega]
  rw [← List.append_assoc]
  show padDigits 4 (n.digitAt n.baseIndex) ++ _ = _
  rw [show n.groupList n.baseIndex (n.intGroups + 1)
      = n.digitAt n.baseIndex :: n.groupList (n.baseIndex + 1) n.intGroups from rfl,
    List.flatMap_cons, digits4_eq_padDigits (hall n.baseIndex)]

private theorem digits4_take {v r : Nat} (h1 : 0 < r) (h2 : r < 4)
    (h : v % 10 ^ (4 - r) = 0) :
    (digits4 v).take r ++ List.replicate (4 - r) '0' = digits4 v := by
  have hr : r = 1 ∨ r = 2 ∨ r = 3 := by omega
  unfold digits4
  rcases hr with rfl | rfl | rfl
  · have h' : v % 1000 = 0 := h
    rw [digitChar_eq_zero (show v / 100 % 10 = 0 from by omega),
      digitChar_eq_zero (show v / 10 % 10 = 0 from by omega),
      digitChar_eq_zero (show v % 10 = 0 from by omega)]
    rfl
  · have h' : v % 100 = 0 := h
    rw [digitChar_eq_zero (show v / 10 % 10 = 0 from by omega),
      digitChar_eq_zero (show v % 10 = 0 from by omega)]
    rfl
  · have h' : v % 10 = 0 := h
    rw [digitChar_eq_zero (show v % 10 = 0 from by omega)]
    rfl

theorem length_fracChars {n : PgNumeric} (k : Nat) : (n.fracChars k).length = k := by
  unfold fracChars
  rw [List.length_take, length_flatMap_digits4, groupList_length]
  omega

theorem alignFrac_fracChars {n : PgNumeric}
    (htail : n.dscale % 4 ≠ 0 →
      n.digitAt (n.weight + 1 + (n.dscale / 4 : Nat)) % 10 ^ (4 - n.dscale % 4) = 0) :
    alignFrac (n.fracChars n.dscale) =
      (n.groupList (n.weight + 1) ((n.dscale + 3) / 4)).flatMap digits4 := by
  show n.fracChars n.dscale ++
    List.replicate ((4 - (n.fracChars n.dscale).length % 4) % 4) '0' = _
  rw [length_fracChars]
  by_cases hr : n.dscale % 4 = 0
  · rw [show ((4 : Nat) - n.dscale % 4) % 4 = 0 from by omega, List.replicate_zero,
      List.append_nil]
    unfold fracChars
    rw [List.take_of_length_le (by
      rw [length_flatMap_digits4, groupList_length]; omega)]
  · rw [show ((4 : Nat) - n.dscale % 4) % 4 = 4 - n.dscale % 4 from by omega]
    have hceil : (n.dscale + 3) / 4 = n.dscale / 4 + 1 := by omega
    have hG : ((n.groupList (n.weight + 1) (n.dscale / 4)).flatMap digits4).length
        = n.dscale - n.dscale % 4 := by
      rw [length_flatMap_digits4, groupList_length]; omega
    unfold fracChars
    rw [hceil, groupList_snoc, List.flatMap_append,
      show ([n.digitAt (n.weight + 1 + (n.dscale / 4 : Nat))] : List Nat).flatMap digits4
        = digits4 (n.digitAt (n.weight + 1 + (n.dscale / 4 : Nat))) from by simp]
    rw [List.take_append, hG,
      show n.dscale - (n.dscale - n.dscale % 4) = n.dscale % 4 from by omega,
      List.take_of_length_le (l := (n.groupList (n.weight + 1) (n.dscale / 4)).flatMap digits4)
        (by rw [hG]; omega),
      List.append_assoc,
      digits4_take (Nat.pos_of_ne_zero hr) (by omega) (htail hr)]



-- ── stripping the alignment's zero groups ─────────────────────────────────

private theorem dropLeadZeros_replicate : ∀ (p : Nat) (l : List UInt16),
    dropLeadZeros (List.replicate p 0 ++ l) = dropLeadZeros l := by
  intro p
  induction p with
  | zero => intro l; rw [List.replicate_zero, List.nil_append]
  | succ j ih =>
    intro l
    rw [List.replicate_succ, List.cons_append]
    show (if ((0 : UInt16) == 0) = true then dropLeadZeros (List.replicate j 0 ++ l)
      else _) = _
    simp only [beq_self_eq_true, if_true, ih l]

private theorem dropLeadZeros_replicate_nil (p : Nat) :
    dropLeadZeros (List.replicate p 0) = [] := by
  rw [← List.append_nil (List.replicate p (0 : UInt16)), dropLeadZeros_replicate]
  rfl

private theorem dropLeadZeros_cons {d : UInt16} (h : d ≠ 0) (rest : List UInt16) :
    dropLeadZeros (d :: rest) = d :: rest := by
  show (if d == 0 then _ else d :: rest) = _
  rw [if_neg (by simpa using h)]

private theorem dropTrailZeros_replicate (l : List UInt16) (q : Nat) :
    dropTrailZeros (l ++ List.replicate q 0) = dropTrailZeros l := by
  unfold dropTrailZeros
  rw [List.reverse_append, List.reverse_replicate, dropLeadZeros_replicate]

private theorem dropTrailZeros_concat {d : UInt16} (h : d ≠ 0) (l : List UInt16) :
    dropTrailZeros (l ++ [d]) = l ++ [d] := by
  unfold dropTrailZeros
  rw [List.reverse_append, show ([d] : List UInt16).reverse = [d] from rfl,
    List.cons_append, List.nil_append, dropLeadZeros_cons h, List.reverse_cons,
    List.reverse_reverse]

-- ── the parsed group list ─────────────────────────────────────────────────

/-- What `fromBinary` and `fromString` both produce, and exactly what the text
form can round-trip: every base-10000 digit in range, no leading or trailing
zero group, zero spelled canonically, and a display scale wide enough to show
every digit. -/
structure Canonical (n : PgNumeric) : Prop where
  /-- Not NaN/±Infinity. -/
  finite : n.special = none
  /-- Every digit is a base-10000 digit. -/
  digitsLt : ∀ d ∈ n.digits, d.toNat < 10000
  /-- No leading zero group. -/
  leadNz : n.digits.size ≠ 0 → n.digitAt 0 ≠ 0
  /-- No trailing zero group. -/
  trailNz : n.digits.size ≠ 0 → n.digitAt ((n.digits.size : Int) - 1) ≠ 0
  /-- Zero carries no sign and no weight. -/
  zeroCanon : n.digits.size = 0 → n.neg = false ∧ n.weight = 0
  /-- The display scale reaches the last digit. -/
  covers : (n.digits.size : Int) ≤ n.weight + 1 + (((n.dscale + 3) / 4 : Nat) : Int)
  /-- A partly-shown final group has nothing but zeros past the cut. -/
  tail : n.dscale % 4 ≠ 0 →
    n.digitAt (n.weight + 1 + (n.dscale / 4 : Nat)) % 10 ^ (4 - n.dscale % 4) = 0

/-- Out-of-range group indices read as `0`, so a bound on the array is a bound
on every group. -/
theorem Canonical.inRange {n : PgNumeric} (hc : Canonical n) : ∀ i, n.digitAt i < 10000 := by
  intro i
  unfold digitAt
  split
  · omega
  · rename_i hi
    by_cases hlt : i.toNat < n.digits.size
    · rw [Array.getElem?_eq_getElem hlt]
      exact hc.digitsLt _ (Array.getElem_mem hlt)
    · rw [Array.getElem?_eq_none (by omega)]
      exact (by decide)

/-- The number of leading zero groups the left-alignment introduced. -/
private def leadPad (n : PgNumeric) : Nat := (-n.weight).toNat

/-- Total base-10000 groups in the rendering. -/
private def totalGroups (n : PgNumeric) : Nat := n.intGroups + 1 + (n.dscale + 3) / 4

private theorem chars_groups {n : PgNumeric} (hc : Canonical n) :
    alignInt n.intChars ++ alignFrac (n.fracChars n.dscale) =
      (n.groupList n.baseIndex n.totalGroups).flatMap digits4 := by
  rw [alignInt_intChars hc.inRange, alignFrac_fracChars hc.tail, ← List.flatMap_append]
  unfold totalGroups
  rw [groupList_append (n.intGroups + 1) ((n.dscale + 3) / 4) n.baseIndex,
    show n.baseIndex + ((n.intGroups + 1 : Nat) : Int) = n.weight + 1 from by
      unfold baseIndex; omega]

private theorem groups_shape {n : PgNumeric} (hc : Canonical n) :
    (n.groupList n.baseIndex n.totalGroups).map UInt16.ofNat =
      List.replicate n.leadPad 0 ++
        (n.digits.toList ++ List.replicate (n.totalGroups - n.leadPad - n.digits.size) 0) := by
  have hbase : n.baseIndex + ((n.leadPad : Nat) : Int) = 0 := by
    unfold baseIndex leadPad intGroups; omega
  have hsum : n.totalGroups = n.leadPad + (n.digits.size +
      (n.totalGroups - n.leadPad - n.digits.size)) := by
    unfold totalGroups leadPad intGroups
    have := hc.covers
    omega
  rw [hsum, groupList_append, hbase, groupList_append,
    groupList_zeros n.leadPad n.baseIndex (by omega),
    groupList_zeros_right _ (0 + (n.digits.size : Nat)) (by omega)]
  have hd := groupList_digits (n := n) n.digits.size 0 (by omega)
  rw [show (((0 : Nat) : Int)) = (0 : Int) from rfl, List.drop_zero,
    List.take_of_length_le (by simp only [Array.length_toList]; omega)] at hd
  rw [List.map_append, List.map_append, hd]
  simp



private theorem length_alignInt_intChars {n : PgNumeric} (hc : Canonical n) :
    (alignInt n.intChars).length = 4 * (n.intGroups + 1) := by
  rw [alignInt_intChars hc.inRange, length_flatMap_digits4, groupList_length]

private theorem raw_groups {n : PgNumeric} (hc : Canonical n) :
    (group4 (alignInt n.intChars ++ alignFrac (n.fracChars n.dscale)) #[]).toList =
      List.replicate n.leadPad 0 ++
        (n.digits.toList ++
          List.replicate (n.totalGroups - n.leadPad - n.digits.size) 0) := by
  rw [chars_groups hc, group4_flatMap _ (groupList_lt hc.inRange _ _)]
  simp only [Array.toList_append, List.nil_append]
  exact groups_shape hc

private theorem dropTrailZeros_self {l : List UInt16}
    (h : ∀ d, l.getLast? = some d → d ≠ 0) : dropTrailZeros l = l := by
  unfold dropTrailZeros
  cases hr : l.reverse with
  | nil =>
    rw [show l = [] from by rw [← List.reverse_reverse l, hr]; rfl]
    rfl
  | cons d u =>
    have hd : d ≠ 0 := h d (by rw [← List.head?_reverse, hr]; rfl)
    rw [dropLeadZeros_cons hd, ← hr, List.reverse_reverse]

theorem ofDigitChars_chars {n : PgNumeric} (hc : Canonical n) :
    ofDigitChars n.neg n.intChars (n.fracChars n.dscale) = n := by
  have hraw := raw_groups hc
  have hlenI := length_alignInt_intChars hc
  have hds := length_fracChars (n := n) n.dscale
  have hlenL : n.digits.toList.length = n.digits.size := Array.length_toList
  unfold ofDigitChars
  rw [hraw, hlenI, hds]
  by_cases hsz : n.digits.size = 0
  · have hnil : n.digits.toList = [] := by
      rw [← Array.length_toList] at hsz
      exact List.eq_nil_of_length_eq_zero hsz
    obtain ⟨hneg, hw⟩ := hc.zeroCanon hsz
    have hsp := hc.finite
    have hde : n.digits = #[] := Array.eq_empty_of_size_eq_zero hsz
    rw [hnil, List.nil_append, dropLeadZeros_replicate, dropLeadZeros_replicate_nil]
    show ofGroups n.neg n.dscale [] _ = n
    unfold ofGroups
    show PgNumeric.mk false #[] 0 n.dscale none = n
    obtain ⟨neg, digits, weight, dscale, special⟩ := n
    simp only at hneg hw hsp hde ⊢
    rw [hneg, hw, hsp, hde]
  · have hd0 : ∀ d rest, n.digits.toList = d :: rest → d ≠ 0 := by
      intro d rest hl hz
      have h := hc.leadNz hsz
      rw [show (0 : Int) = ((0 : Nat) : Int) from rfl,
        digitAt_lt (n := n) (s := 0) (by omega)] at h
      apply h
      rw [show n.digits[0]'(by omega) = n.digits.toList[0]'(by omega) from
        (Array.getElem_toList _).symm]
      simp only [hl, List.getElem_cons_zero, hz]
      rfl
    have hdlast : ∀ d, n.digits.toList.getLast? = some d → d ≠ 0 := by
      intro d hg hz
      have h := hc.trailNz hsz
      rw [show ((n.digits.size : Int) - 1) = (((n.digits.size - 1 : Nat)) : Int) from by omega,
        digitAt_lt (n := n) (s := n.digits.size - 1) (by omega)] at h
      apply h
      rw [List.getLast?_eq_getElem?,
        List.getElem?_eq_getElem (by omega)] at hg
      rw [show n.digits[n.digits.size - 1]'(by omega)
          = n.digits.toList[n.digits.size - 1]'(by omega) from
        (Array.getElem_toList _).symm]
      have : n.digits.toList[n.digits.toList.length - 1]'(by omega) = d :=
        Option.some.inj hg
      rw [show n.digits.toList[n.digits.size - 1]'(by omega)
          = n.digits.toList[n.digits.toList.length - 1]'(by omega) from by
        first | rfl | (congr 1; omega),
        this, hz]
      rfl
    cases hl : n.digits.toList with
    | nil => exact absurd (by rw [← hlenL, hl]; rfl) hsz
    | cons d0 rest =>
      rw [List.cons_append, dropLeadZeros_replicate,
        dropLeadZeros_cons (hd0 d0 rest hl)]
      show ofGroups n.neg n.dscale (d0 :: (rest ++ _)) _ = n
      unfold ofGroups
      rw [show (d0 :: (rest ++ List.replicate (n.totalGroups - n.leadPad - n.digits.size) 0))
          = n.digits.toList ++ List.replicate (n.totalGroups - n.leadPad - n.digits.size) 0 from by
        rw [hl, List.cons_append],
        dropTrailZeros_replicate, dropTrailZeros_self hdlast, hl]
      show PgNumeric.mk n.neg (d0 :: rest).toArray _ n.dscale none = n
      have hrl : rest.length + 1 = n.digits.size := by rw [← hlenL, hl]; rfl
      have hw : ((4 * (n.intGroups + 1) : Nat) : Int) / 4 - 1 -
          (((List.replicate n.leadPad (0 : UInt16) ++
              (d0 :: rest ++ List.replicate
                (n.totalGroups - n.leadPad - n.digits.size) 0)).length
            - (d0 :: rest ++ List.replicate
                (n.totalGroups - n.leadPad - n.digits.size) 0).length : Nat) : Int)
          = n.weight := by
        simp only [List.length_append, List.length_replicate, List.length_cons]
        unfold leadPad intGroups
        have := hc.covers
        omega
      have hsp := hc.finite
      rw [hw, ← hl, Array.toArray_toList]
      obtain ⟨neg, digits, weight, dscale, special⟩ := n
      simp only at hsp ⊢
      rw [hsp]


-- ── every rendered character is a digit, `-` or `.` ───────────────────────

private theorem isAsciiDigit_digitChar' (x : Nat) : isAsciiDigit (digitChar x) = true := by
  rw [← digitChar_mod]
  exact isAsciiDigit_digitChar (Nat.mod_lt _ (by omega))

private theorem digits_of_mem_digits4 {v : Nat} {c : Char} (h : c ∈ digits4 v) :
    isAsciiDigit c = true := by
  unfold digits4 at h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl <;> exact isAsciiDigit_digitChar' _

private theorem digits_of_mem_flatMap : ∀ (l : List Nat) (c : Char),
    c ∈ l.flatMap digits4 → isAsciiDigit c = true := by
  intro l
  induction l with
  | nil => intro c h; exact absurd h List.not_mem_nil
  | cons v t ih =>
    intro c h
    rw [List.flatMap_cons, List.mem_append] at h
    rcases h with h | h
    · exact digits_of_mem_digits4 h
    · exact ih c h

theorem digits_of_mem_fracChars {n : PgNumeric} {k : Nat} {c : Char}
    (h : c ∈ n.fracChars k) : isAsciiDigit c = true := by
  unfold fracChars at h
  exact digits_of_mem_flatMap _ c (List.mem_of_mem_take h)

theorem digits_of_mem_intChars {n : PgNumeric} (hall : ∀ i, n.digitAt i < 10000)
    {c : Char} (h : c ∈ n.intChars) : isAsciiDigit c = true := by
  unfold intChars at h
  rw [List.mem_append] at h
  rcases h with h | h
  · exact isAsciiDigit_of_mem_natDigits _ c h
  · rw [flatMap_padDigits_eq _ (groupList_lt hall _ _)] at h
    exact digits_of_mem_flatMap _ c h

theorem intChars_ne_nil {n : PgNumeric} : n.intChars ≠ [] := by
  unfold intChars
  exact fun h => absurd (List.append_eq_nil_iff.mp h).1 (natDigits_ne_nil _)

theorem chars_charset {n : PgNumeric} (hall : ∀ i, n.digitAt i < 10000) :
    ∀ c ∈ n.chars, isAsciiDigit c = true ∨ c = '-' ∨ c = '.' := by
  intro c hc
  unfold chars at hc
  rw [List.mem_append, List.mem_append] at hc
  rcases hc with (hc | hc) | hc
  · split at hc
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      exact Or.inr (Or.inl hc)
    · exact absurd hc List.not_mem_nil
  · exact Or.inl (digits_of_mem_intChars hall hc)
  · split at hc
    · exact absurd hc List.not_mem_nil
    · rcases List.mem_cons.mp hc with rfl | hc
      · exact Or.inr (Or.inr rfl)
      · exact Or.inl (digits_of_mem_fracChars hc)

private theorem no_space_of_charset {l : List Char}
    (h : ∀ c ∈ l, isAsciiDigit c = true ∨ c = '-' ∨ c = '.') :
    ∀ c ∈ l, isAsciiSpace c = false := by
  intro c hc
  rcases h c hc with h | rfl | rfl
  · cases hs : isAsciiSpace c with
    | false => rfl
    | true =>
      exfalso
      simp only [isAsciiSpace, Bool.or_eq_true, beq_iff_eq] at hs
      rcases hs with ((rfl | rfl) | rfl) | rfl <;> exact absurd h (by decide)
  · rfl
  · rfl

private theorem specialOf_eq_none {l : List Char}
    (h : ∀ c ∈ l, isAsciiDigit c = true ∨ c = '-' ∨ c = '.') : specialOf l = none := by
  unfold specialOf
  split
  · exact absurd (h 'N' (by simp)) (by decide)
  · exact absurd (h 'I' (by simp)) (by decide)
  · exact absurd (h 'I' (by simp)) (by decide)
  · exact absurd (h 'i' (by simp)) (by decide)
  · exact absurd (h 'I' (by simp)) (by decide)
  · exact absurd (h 'i' (by simp)) (by decide)
  · rfl



private theorem dot_not_mem_intChars {n : PgNumeric} (hall : ∀ i, n.digitAt i < 10000) :
    '.' ∉ n.intChars := fun h => absurd (digits_of_mem_intChars hall h) (by decide)

private theorem dot_not_mem_fracChars {n : PgNumeric} {k : Nat} :
    '.' ∉ n.fracChars k := fun h => absurd (digits_of_mem_fracChars h) (by decide)

private theorem all_digits_intChars {n : PgNumeric} (hall : ∀ i, n.digitAt i < 10000) :
    n.intChars.all isAsciiDigit = true :=
  List.all_eq_true.mpr (fun c hc => digits_of_mem_intChars hall hc)

private theorem all_digits_fracChars {n : PgNumeric} {k : Nat} :
    (n.fracChars k).all isAsciiDigit = true :=
  List.all_eq_true.mpr (fun c hc => digits_of_mem_fracChars hc)

private theorem if_isEmpty_intChars {n : PgNumeric} :
    (if n.intChars.isEmpty then ['0'] else n.intChars) = n.intChars := by
  cases hi : n.intChars with
  | nil => exact absurd hi intChars_ne_nil
  | cons c t => rfl

private theorem ofSigned_body {n : PgNumeric} (hc : Canonical n) (orig : String) :
    ofSigned orig n.neg (n.intChars ++
      (if n.dscale = 0 then [] else '.' :: n.fracChars n.dscale)) = .ok n := by
  unfold ofSigned
  by_cases hd : n.dscale = 0
  · rw [if_pos hd, List.append_nil,
      List.splitOn_eq_singleton (dot_not_mem_intChars hc.inRange)]
    show ofParts orig n.neg n.intChars [] = _
    unfold ofParts
    rw [if_pos (by rw [if_isEmpty_intChars, all_digits_intChars hc.inRange]; rfl),
      if_isEmpty_intChars,
      show ([] : List Char) = n.fracChars n.dscale from by rw [hd]; rfl,
      ofDigitChars_chars hc]
  · rw [if_neg hd, List.splitOn_append_cons_self_of_not_mem
      (dot_not_mem_intChars hc.inRange),
      List.splitOn_eq_singleton (dot_not_mem_fracChars (n := n) (k := n.dscale))]
    show ofParts orig n.neg n.intChars (n.fracChars n.dscale) = _
    unfold ofParts
    rw [if_pos (by
      rw [if_isEmpty_intChars, all_digits_intChars hc.inRange,
        all_digits_fracChars (n := n) (k := n.dscale)]
      rfl),
      if_isEmpty_intChars, ofDigitChars_chars hc]

private theorem ofSigned_body' {n : PgNumeric} (hc : Canonical n) (orig : String)
    (b : Bool) (hb : b = n.neg) :
    ofSigned orig b (n.intChars ++
      (if n.dscale = 0 then [] else '.' :: n.fracChars n.dscale)) = .ok n := by
  rw [hb]; exact ofSigned_body hc orig

/-- **A `numeric` renders and parses back to itself.** Every base-10000 digit,
the sign, the weight and the display scale are recovered exactly — no silent
precision loss — for every canonical value: digits in range, no leading or
trailing zero group, zero spelled canonically, and a display scale wide enough
to show the last digit. -/
theorem fromString_toString {n : PgNumeric} (hc : Canonical n) :
    fromString n.toString = .ok n := by
  have hcs := chars_charset hc.inRange
  have hns := no_space_of_charset hcs
  unfold fromString
  rw [toString_eq hc.finite, String.toList_ofList, trimAsciiChars_of_no_space hns]
  unfold ofChars
  rw [specialOf_eq_none hcs]
  show ofDecimalChars (String.ofList n.chars) n.chars = _
  unfold chars
  cases hneg : n.neg with
  | true =>
    rw [if_pos rfl]
    show ofDecimalChars _ ('-' :: (n.intChars ++ _)) = _
    simp only [ofDecimalChars, beq_self_eq_true, if_true]
    exact ofSigned_body' hc _ true hneg.symm
  | false =>
    rw [if_neg (by simp), List.nil_append]
    cases hi : n.intChars with
    | nil => exact absurd hi intChars_ne_nil
    | cons c t =>
      have hdig : isAsciiDigit c = true :=
        digits_of_mem_intChars hc.inRange (by rw [hi]; exact List.mem_cons_self ..)
      rw [List.cons_append]
      simp only [ofDecimalChars, beq_false_of_ne (show c ≠ '-' from by
          intro h; rw [h] at hdig; exact absurd hdig (by decide)),
        beq_false_of_ne (show c ≠ '+' from by
          intro h; rw [h] at hdig; exact absurd hdig (by decide))]
      rw [← List.cons_append, ← hi]
      exact ofSigned_body' hc _ false hneg.symm



/-- Non-vacuity: `12345.678` as PostgreSQL sends it — base-10000 digits
`1`, `2345`, `6780` with weight 1 and display scale 3 — is canonical, so the
law above applies to it. (`Test/CodecTest.lean` checks the rendering itself;
`natDigits` is well-founded recursion, which the kernel will not evaluate.) -/
example : Canonical { neg := false, digits := #[1, 2345, 6780], weight := 1, dscale := 3 } := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

end PgNumeric

end Pg
