import Pg.Types.Codec
import Test.Support.Hex

/-!
Codec known-answer tests: text and binary wire formats for the core type set,
including NULL/Option handling, PG-epoch temporal conversions, numeric
base-10000 layout, interval triples, and 1-D arrays.
-/

open Pg
open Pg.TestSupport
open Std.Time

def expect (cond : Bool) (msg : String) : IO Unit := do
  unless cond do throw (IO.userError msg)

def expectOk [BEq α] [Repr α] (got : Except String α) (want : α) (label : String) : IO Unit := do
  match got with
  | .ok v =>
    unless v == want do
      throw (IO.userError s!"{label}: got {repr v}, want {repr want}")
  | .error e => throw (IO.userError s!"{label}: unexpected error {e}")

def expectErr (got : Except String α) (label : String) : IO Unit := do
  match got with
  | .ok _ => throw (IO.userError s!"{label}: expected error, got ok")
  | .error _ => pure ()

def dText (α : Type) [PgDecode α] (oid : UInt32) (s : String) : Except String α :=
  PgDecode.decodeText oid s

def dBin (α : Type) [PgDecode α] (oid : UInt32) (b : ByteArray) : Except String α :=
  PgDecode.decodeBinary oid b

def encText (α : Type) [PgEncode α] (x : α) : String :=
  match PgEncode.encode x with
  | some bytes => (String.fromUTF8? bytes).getD "<bad utf8>"
  | none => "<null>"

def main : IO Unit := do
  -- ── integers ────────────────────────────────────────────────────────────
  expectOk (dText Int 0 "-42") (-42) "int text"
  expectErr (dText Int 0 "4x2") "int text junk"
  expectOk (dBin Int 0 (hex "00 2a")) 42 "int2 binary widen"
  expectOk (dBin Int 0 (hex "ff ff ff ff ff ff ff f6")) (-10) "int8 binary negative"
  expectOk (dBin Int64 0 (hex "7f ff ff ff ff ff ff ff")) 9223372036854775807 "int8 max"
  expectOk (dBin Int32 0 (hex "80 00 00 00")) (-2147483648) "int4 min"
  expectErr (dText Int32 0 "2147483648") "int4 range"
  expectErr (dText Int16 0 "40000") "int2 range"
  expectErr (dBin Int 0 (hex "01 02 03")) "int bad width"
  expect (encText Int (-7) == "-7") "int encode"

  -- ── floats ──────────────────────────────────────────────────────────────
  expectOk (dBin Float 0 (hex "3f f8 00 00 00 00 00 00")) 1.5 "float8 binary"
  expectOk (dBin Float 0 (hex "c0 20 00 00")) (-2.5) "float4 binary"
  expectOk (dText Float 0 "1.5") 1.5 "float text"
  expectOk (dText Float 0 "-1.5e2") (-150.0) "float text exponent"
  expectOk (dText Float 0 "0.25") 0.25 "float text fraction"
  match dText Float 0 "NaN" with
  | .ok v => expect v.isNaN "float NaN"
  | .error e => throw (IO.userError s!"float NaN: {e}")
  match dText Float 0 "-Infinity" with
  | .ok v => expect (v < 0 && v.isInf) "float -inf"
  | .error e => throw (IO.userError s!"float -inf: {e}")
  expectErr (dText Float 0 "abc") "float junk"

  -- ── bool, string, bytea ─────────────────────────────────────────────────
  expectOk (dText Bool 0 "t") true "bool t"
  expectOk (dText Bool 0 "f") false "bool f"
  expectOk (dBin Bool 0 (hex "01")) true "bool binary"
  expectErr (dBin Bool 0 (hex "01 00")) "bool width"
  expectOk (dText String Oid.text "héllo") "héllo" "string text"
  expectOk (dBin String Oid.text (ascii "plain")) "plain" "string binary"
  expectOk (dBin String Oid.uuid (hex "a0 ee bc 99 9c 0b 4e f8 bb 6d 6b b9 bd 38 0a 11"))
    "a0eebc99-9c0b-4ef8-bb6d-6bb9bd380a11" "uuid binary"
  expectErr (dBin String Oid.uuid (hex "00 01")) "uuid width"
  expectOk (dBin String Oid.jsonb (hex "01" ++ ascii "{\"a\":1}")) "{\"a\":1}" "jsonb version strip"
  expectErr (dBin String Oid.jsonb (hex "02" ++ ascii "{}")) "jsonb bad version"
  expectOk (dText ByteArray 0 "\\xdeadbeef") (hex "de ad be ef") "bytea text"
  expectErr (dText ByteArray 0 "deadbeef") "bytea missing prefix"
  expectOk (dBin ByteArray 0 (hex "00 ff")) (hex "00 ff") "bytea binary"

  -- ── NULL and Option ─────────────────────────────────────────────────────
  expectOk (decodeValue (α := Option Int) 0 0 none) none "null option"
  expectErr (decodeValue (α := Int) 0 0 none) "null non-option"
  expectOk (decodeValue (α := Option String) Oid.text 0 (some ByteArray.empty))
    (some "") "empty string is not NULL"

  -- ── temporal ────────────────────────────────────────────────────────────
  expectOk (dText PlainDate 0 "2024-01-15")
    (PlainDate.ofDaysSinceUNIXEpoch (uv (8780 + pgEpochDays))) "date text"
  expectOk (dBin PlainDate 0 (hex "00 00 22 4c"))
    (PlainDate.ofDaysSinceUNIXEpoch (uv (8780 + pgEpochDays))) "date binary"
  expect (encText PlainDate (PlainDate.ofDaysSinceUNIXEpoch (uv (8780 + pgEpochDays)))
    == "2024-01-15") "date render"
  expectErr (dText PlainDate 0 "infinity") "date infinity text"
  expectErr (dBin PlainDate 0 (hex "7f ff ff ff")) "date infinity binary"
  expectErr (dText PlainDate 0 "2024-02-30") "date invalid day"

  expectOk (dText PlainTime 0 "13:04:05.5")
    (PlainTime.ofNanoseconds (uv 47045500000000)) "time text"
  expectOk (dBin PlainTime 0 (hex "00 00 00 0a f4 21 5c 60"))
    (PlainTime.ofNanoseconds (uv 47045500000000)) "time binary"
  expect (encText PlainTime (PlainTime.ofNanoseconds (uv 47045500000000))
    == "13:04:05.500000") "time render"

  -- timestamp: binary 1,000,000 µs past the PG epoch = 2000-01-01 00:00:01
  expect (encText PlainDateTime (dateTimeOfPgMicros 1000000)
    == "2000-01-01 00:00:01") "timestamp epoch"
  expectOk (dBin PlainDateTime 0 (hex "00 00 00 00 00 0f 42 40"))
    (dateTimeOfPgMicros 1000000) "timestamp binary"
  expectOk (dText PlainDateTime 0 "2000-01-01 00:00:01")
    (dateTimeOfPgMicros 1000000) "timestamp text"
  expectErr (dBin PlainDateTime 0 (hex "7f ff ff ff ff ff ff ff")) "timestamp infinity"

  -- timestamptz: +02 offset shifts to UTC
  match dText Timestamp 0 "2024-01-15 10:00:00+02" with
  | .error e => throw (IO.userError s!"tstz text: {e}")
  | .ok ts =>
    expect (encText Timestamp ts == "2024-01-15 08:00:00+00") "tstz offset to UTC"
  match dText Timestamp 0 "2024-01-15 03:30:00-05:30" with
  | .error e => throw (IO.userError s!"tstz negative offset: {e}")
  | .ok ts =>
    expect (encText Timestamp ts == "2024-01-15 09:00:00+00") "tstz negative offset"
  expectOk (dBin Timestamp 0 (hex "00 00 00 00 00 0f 42 40"))
    (Timestamp.ofNanosecondsSinceUnixEpoch (uv ((pgEpochSeconds + 1) * 1000000000)))
    "tstz binary"

  -- ── numeric ─────────────────────────────────────────────────────────────
  for s in ["0", "42", "-1.5", "0.00001", "12345.678", "9999.9999", "1000000",
            "0.000", "123456789012345678901234567890.1"] do
    match PgNumeric.fromString s with
    | .error e => throw (IO.userError s!"numeric parse {s}: {e}")
    | .ok n =>
      expect (n.toString == s) s!"numeric roundtrip {s} (got {n.toString})"
      expectOk (dBin PgNumeric 0 n.toBinary) n s!"numeric binary roundtrip {s}"
  expectOk (dBin PgNumeric 0 (hex "00 03 00 01 00 00 00 03 00 01 09 29 1a 7c"))
    (⟨false, #[1, 2345, 6780], 1, 3, none⟩ : PgNumeric) "numeric binary KAT"
  match PgNumeric.fromString "NaN" with
  | .ok n => expect (n.special == some .nan && n.toString == "NaN") "numeric NaN"
  | .error e => throw (IO.userError s!"numeric NaN: {e}")
  match PgNumeric.fromString "-Infinity" with
  | .ok n =>
    expect (n.toString == "-Infinity") "numeric -inf"
    expectOk (dBin PgNumeric 0 n.toBinary) n "numeric -inf binary"
  | .error e => throw (IO.userError s!"numeric -inf: {e}")
  expectErr (PgNumeric.fromString "1e10") "numeric rejects e-notation"
  -- the value-level direction `PgNumeric.fromString_toString` proves (the
  -- kernel cannot evaluate `natDigits`, so this half is checked at runtime)
  for n in [(⟨false, #[1, 2345, 6780], 1, 3, none⟩ : PgNumeric),
            ⟨true, #[5000], -1, 4, none⟩, ⟨false, #[], 0, 0, none⟩,
            ⟨false, #[], 0, 2, none⟩, ⟨true, #[12, 3400], 2, 0, none⟩] do
    expectOk (PgNumeric.fromString n.toString) n s!"numeric text roundtrip {n.toString}"

  -- ── interval ────────────────────────────────────────────────────────────
  expectOk (dText PgInterval 0 "1 year 2 mons 3 days 04:05:06.789")
    ⟨14, 3, 14706789000⟩ "interval text"
  expectOk (dText PgInterval 0 "-00:00:01.5") ⟨0, 0, -1500000⟩ "interval negative time"
  expectOk (dText PgInterval 0 "00:00:00") ⟨0, 0, 0⟩ "interval zero"
  expectOk (dBin PgInterval 0 (hex "00 00 00 00 00 0f 42 40 00 00 00 00 00 00 00 00"))
    ⟨0, 0, 1000000⟩ "interval binary KAT"
  for iv in [(⟨14, 3, 14706789000⟩ : PgInterval), ⟨-2, -3, -5000001⟩, ⟨0, 0, 0⟩] do
    expectOk (dBin PgInterval 0 iv.toBinary) iv s!"interval binary roundtrip {iv.toString}"
    expectOk (dText PgInterval 0 iv.toString) iv s!"interval text roundtrip {iv.toString}"
  -- `PgInterval.fromString_toString` holds for every interval; spot-check the
  -- shapes with zero components, which take the other branches of `tokens`
  for iv in [(⟨5, 0, 0⟩ : PgInterval), ⟨0, 7, 0⟩, ⟨0, 0, -1⟩, ⟨-1, -1, -1⟩,
             ⟨0, 0, 90061000001⟩] do
    expectOk (PgInterval.fromString iv.toString) iv s!"interval text roundtrip {iv.toString}"

  -- ── arrays ──────────────────────────────────────────────────────────────
  expectOk (dText (Array Int) Oid.int4Array "{1,2,3}") #[1, 2, 3] "int array text"
  expectOk (dText (Array (Option Int)) Oid.int4Array "{1,NULL,3}")
    #[some 1, none, some 3] "int array with NULL"
  expectErr (dText (Array Int) Oid.int4Array "{1,NULL}") "NULL in strict array"
  expectOk (dText (Array String) Oid.textArray "{}") #[] "empty array"
  expectOk (dText (Array String) Oid.textArray "{plain,\"quo\\\"ted\",\"NULL\"}")
    #["plain", "quo\"ted", "NULL"] "quoted array elements"
  expectOk (dText (Array (Option String)) Oid.textArray "{NULL,\"NULL\"}")
    #[none, some "NULL"] "NULL vs quoted NULL"
  expectOk (dBin (Array (Option Int)) Oid.int4Array
    (hex "00 00 00 01 00 00 00 01 00 00 00 17 00 00 00 02 00 00 00 01 00 00 00 04 00 00 00 01 ff ff ff ff"))
    #[some 1, none] "array binary KAT"
  expectOk (dBin (Array Int) Oid.int4Array (hex "00 00 00 00 00 00 00 00 00 00 00 17"))
    #[] "array binary empty"
  expectErr (dText (Array Int) 0 "1,2") "not an array literal"
  -- the array renderer: every non-NULL element is quoted, so "NULL"-as-text
  -- survives, and quotes/backslashes are escaped
  expect (encText (Array (Option String)) #[some "a", none, some "NULL"]
    == "{\"a\",NULL,\"NULL\"}") "array text render"
  expect (encText (Array (Option String)) #[] == "{}") "empty array render"
  for a in [#[some "a", none, some "NULL"], #[], #[some "quo\"te\\back", some " sp "],
      #[none]] do
    expectOk (parseArrayText (renderArrayText a.toList)) a
      s!"array render/parse roundtrip {renderArrayText a.toList}"

  IO.println "all codec assertions passed"
