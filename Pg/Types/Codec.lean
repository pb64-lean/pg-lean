module

public import Std.Time
public import Pg.Protocol.Message
public import Pg.Crypto.Hex
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

-- ── decimal digit strings ─────────────────────────────────────────────────

/-!
PostgreSQL's temporal text formats are fixed-width zero-padded decimal fields,
so the roundtrip proofs have to walk digits. Neither `Nat.repr` nor
`String.toNat?` can carry that: `Nat.digitChar` is not exposed to the kernel,
and core ships no lemma about `String.toNat?` of a zero-padded argument. These
four functions render and parse exactly the same decimal strings while staying
kernel-visible.
-/

@[expose] def isAsciiDigit (c : Char) : Bool := 48 ≤ c.toNat && c.toNat ≤ 57

@[expose] def digitChar (d : Nat) : Char := Char.ofNat (48 + d % 10)

/-- Decimal digits of `n`, most significant first (`0` is `['0']`) — the same
characters `toString n` produces. -/
def natDigits (n : Nat) : List Char :=
  if n < 10 then [digitChar n] else natDigits (n / 10) ++ [digitChar (n % 10)]
termination_by n
decreasing_by exact Nat.div_lt_self (by omega) (by omega)

/-- `n` in decimal, left-padded with `'0'` to at least `width` characters
(never truncated — a wider value keeps all its digits, as PostgreSQL does with
5-digit years). -/
def padDigits (width n : Nat) : List Char :=
  List.replicate (width - (natDigits n).length) '0' ++ natDigits n

/-- Fold a decimal digit list onto an accumulator; `none` on any non-digit. -/
def natOfDigits (acc : Nat) : List Char → Option Nat
  | [] => some acc
  | c :: rest =>
    if isAsciiDigit c then natOfDigits (acc * 10 + (c.toNat - 48)) rest else none

/-- A whole decimal field: at least one character, all of them digits. -/
def natOfDigitsFull : List Char → Option Nat
  | [] => none
  | chars => natOfDigits 0 chars

-- ── temporal types ─────────────────────────────────────────────────────────

def parseNatField (s : String) (what : String) : Except String Nat :=
  match natOfDigitsFull s.toList with
  | some v => pure v
  | none => throw s!"bad {what}: {s}"

def rejectInfinity (s : String) : Except String Unit := do
  if s == "infinity" || s == "-infinity" then
    throw "date/timestamp infinity is not representable"

/-- Split a string at every occurrence of one character.

Deliberately not `String.splitOn`: `String.splitOnAux` is `@[irreducible]` and
core ships no lemmas about it, so a `String.splitOn`-based parser is opaque to
the kernel. `List.splitOn` has a full lemma set and agrees with it for a
single-character separator. (Same trick as `Pg.Sasl.Scram.splitOnChar`.) -/
def splitOnChar (c : Char) (s : String) : List String :=
  (s.toList.splitOn c).map String.ofList

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

@[expose] def isAsciiSpace (c : Char) : Bool :=
  c == ' ' || c == '\t' || c == '\n' || c == '\r'

/-- Trim ASCII whitespace on the character list. `String.trimAscii` goes
through `String.Slice`, which the kernel cannot follow. -/
def trimAsciiChars (l : List Char) : List Char :=
  ((l.dropWhile isAsciiSpace).reverse.dropWhile isAsciiSpace).reverse

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
### Decimal digit strings

The temporal text codecs are proved through these: `natOfDigits` reads back
exactly what `natDigits`/`padDigits` wrote, at any padding width.
-/

theorem toNat_ofNat_ascii {n : Nat} (h : n ≤ 127) : (Char.ofNat n).toNat = n := by
  show (Char.ofNat n).val.toNat = n
  unfold Char.ofNat
  rw [dif_pos (by unfold Nat.isValidChar; omega)]
  unfold Char.ofNatAux
  simp [UInt32.toNat]

theorem toNat_digitChar {d : Nat} (h : d < 10) : (digitChar d).toNat = 48 + d := by
  unfold digitChar
  rw [Nat.mod_eq_of_lt h, toNat_ofNat_ascii (by omega)]

theorem isAsciiDigit_digitChar {d : Nat} (h : d < 10) :
    isAsciiDigit (digitChar d) = true := by
  unfold isAsciiDigit
  rw [toNat_digitChar h]
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  omega

theorem natOfDigits_append : ∀ (l₁ : List Char) (acc : Nat) (l₂ : List Char),
    natOfDigits acc (l₁ ++ l₂)
      = (natOfDigits acc l₁).bind (fun a => natOfDigits a l₂) := by
  intro l₁
  induction l₁ with
  | nil => intro acc l₂; rfl
  | cons c t ih =>
    intro acc l₂
    simp only [List.cons_append, natOfDigits]
    split
    · exact ih _ _
    · rfl

/-- `natDigits` is never empty, so a rendered field always has a digit. -/
theorem natDigits_ne_nil (n : Nat) : natDigits n ≠ [] := by
  unfold natDigits
  split
  · exact List.cons_ne_nil _ _
  · exact List.append_ne_nil_of_right_ne_nil _ (List.cons_ne_nil _ _)

theorem natOfDigits_natDigits : ∀ (n : Nat) (acc : Nat),
    natOfDigits acc (natDigits n) = some (acc * 10 ^ (natDigits n).length + n) := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro acc
    by_cases h : n < 10
    · have hd : natDigits n = [digitChar n] := by rw [natDigits, if_pos h]
      rw [hd]
      simp only [natOfDigits, isAsciiDigit_digitChar h, if_pos, List.length_cons,
        List.length_nil, toNat_digitChar h]
      congr 1
      omega
    · have h10 : 10 ≤ n := by omega
      have hmod : n % 10 < 10 := Nat.mod_lt _ (by omega)
      have hd : natDigits n = natDigits (n / 10) ++ [digitChar (n % 10)] := by
        rw [natDigits, if_neg h]
      rw [hd, natOfDigits_append, ih (n / 10) (Nat.div_lt_self (by omega) (by omega)) acc]
      simp only [Option.bind_some, natOfDigits, isAsciiDigit_digitChar hmod, if_pos,
        toNat_digitChar hmod, List.length_append, List.length_cons, List.length_nil]
      congr 1
      rw [show 48 + n % 10 - 48 = n % 10 from by omega, Nat.pow_succ,
        Nat.add_mul, Nat.mul_assoc, Nat.add_assoc, Nat.div_add_mod']

theorem natOfDigits_zeros : ∀ (k acc : Nat),
    natOfDigits acc (List.replicate k '0') = some (acc * 10 ^ k) := by
  intro k
  induction k with
  | zero => intro acc; simp only [List.replicate_zero, natOfDigits, Nat.pow_zero, Nat.mul_one]
  | succ j ih =>
    intro acc
    have hz : ('0' : Char).toNat = 48 := by decide
    have hdig : isAsciiDigit '0' = true := by decide
    rw [List.replicate_succ]
    simp only [natOfDigits, hdig, if_pos, hz]
    rw [ih (acc * 10 + (48 - 48))]
    congr 1
    rw [show (48 : Nat) - 48 = 0 from rfl, Nat.add_zero, Nat.pow_succ, Nat.mul_assoc,
      Nat.mul_comm (10 : Nat) (10 ^ j)]

/-- **A padded decimal field reads back as the number it was rendered from**,
at any width. -/
theorem natOfDigits_padDigits (width n : Nat) :
    natOfDigits 0 (padDigits width n) = some n := by
  unfold padDigits
  rw [natOfDigits_append, natOfDigits_zeros, Option.bind_some, natOfDigits_natDigits]
  simp

theorem natOfDigitsFull_padDigits (width n : Nat) :
    natOfDigitsFull (padDigits width n) = some n := by
  have hval := natOfDigits_padDigits width n
  cases hl : padDigits width n with
  | nil => exact absurd (List.append_eq_nil_iff.mp hl).2 (natDigits_ne_nil n)
  | cons c t =>
    rw [hl] at hval
    exact hval

theorem parseNatField_padDigits (width n : Nat) (what : String) :
    parseNatField (String.ofList (padDigits width n)) what = .ok n := by
  unfold parseNatField
  rw [String.toList_ofList, natOfDigitsFull_padDigits]
  rfl

/-- Every character of a rendered decimal field is a digit — which is what
makes the `-`, `:` and `.` separators unambiguous. -/
theorem isAsciiDigit_of_mem_natDigits : ∀ (n : Nat) (c : Char),
    c ∈ natDigits n → isAsciiDigit c = true := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro c hc
    by_cases h : n < 10
    · rw [natDigits, if_pos h] at hc
      rcases List.mem_singleton.mp hc with rfl
      exact isAsciiDigit_digitChar h
    · rw [natDigits, if_neg h] at hc
      rcases List.mem_append.mp hc with hc | hc
      · exact ih (n / 10) (Nat.div_lt_self (by omega) (by omega)) c hc
      · rcases List.mem_singleton.mp hc with rfl
        exact isAsciiDigit_digitChar (Nat.mod_lt _ (by omega))

theorem isAsciiDigit_of_mem_padDigits {width n : Nat} {c : Char}
    (hc : c ∈ padDigits width n) : isAsciiDigit c = true := by
  unfold padDigits at hc
  rcases List.mem_append.mp hc with hc | hc
  · rw [List.eq_of_mem_replicate hc]; decide
  · exact isAsciiDigit_of_mem_natDigits n c hc

/-- A separator that is not a digit never occurs inside a rendered field. -/
theorem ne_of_mem_padDigits {width n : Nat} {sep : Char}
    (hsep : isAsciiDigit sep = false) : ∀ c ∈ padDigits width n, c ≠ sep := by
  intro c hc heq
  have hd := isAsciiDigit_of_mem_padDigits hc
  rw [heq, hsep] at hd
  exact Bool.false_ne_true hd

/-- A decimal rendering of `n < 10^(k+1)` is at most `k+1` characters. -/
theorem natDigits_length_le : ∀ (k n : Nat), n < 10 ^ (k + 1) →
    (natDigits n).length ≤ k + 1 := by
  intro k
  induction k with
  | zero =>
    intro n h
    rw [Nat.pow_one] at h
    rw [natDigits, if_pos h]
    simp
  | succ j ih =>
    intro n h
    by_cases hs : n < 10
    · rw [natDigits, if_pos hs]
      simp only [List.length_cons, List.length_nil]
      omega
    · rw [natDigits, if_neg hs]
      have hdiv : n / 10 < 10 ^ (j + 1) := by
        have : (10 : Nat) ^ (j + 1 + 1) = 10 ^ (j + 1) * 10 := Nat.pow_succ ..
        omega
      have := ih (n / 10) hdiv
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega

theorem padDigits_length {width n : Nat} (h : (natDigits n).length ≤ width) :
    (padDigits width n).length = width := by
  unfold padDigits
  rw [List.length_append, List.length_replicate]
  omega

theorem padDigits_ne_nil (width n : Nat) : padDigits width n ≠ [] :=
  fun h => absurd (List.append_eq_nil_iff.mp h).2 (natDigits_ne_nil n)

theorem not_mem_padDigits {width n : Nat} {sep : Char}
    (hsep : isAsciiDigit sep = false) : sep ∉ padDigits width n :=
  fun hmem => (ne_of_mem_padDigits hsep sep hmem) rfl

/-!
### Temporal text roundtrips

PostgreSQL renders `date` and `time` as fixed-width decimal fields; these laws
say pg-lean's parser recovers exactly what its renderer wrote. Floats are
deliberately absent: `toString`/`parseFloat` is *not* an unconditional IEEE-754
roundtrip (shortest-representation printing plus decimal-to-binary rounding),
and stating the true law needs real-arithmetic support this repository does not
have (core + Std only, no Mathlib).
-/

theorem splitOnChar_singleton {c : Char} {s : String} (h : c ∉ s.toList) :
    splitOnChar c s = [s] := by
  unfold splitOnChar
  rw [List.splitOn_eq_singleton h]
  simp only [List.map_cons, List.map_nil, String.ofList_toList]

theorem splitOnChar_cons {c : Char} {p rest : List Char} (h : c ∉ p) :
    splitOnChar c (String.ofList (p ++ c :: rest)) =
      String.ofList p :: splitOnChar c (String.ofList rest) := by
  unfold splitOnChar
  rw [String.toList_ofList, List.splitOn_append_cons_self_of_not_mem h,
    String.toList_ofList, List.map_cons]

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

end Pg
