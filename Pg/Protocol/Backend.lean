module

public import Pg.Protocol.Message
public import Pg.Crypto.Hex

public section

namespace Pg
namespace Protocol

/-!
Typed backend messages and their payload parsers. `Backend.decode` turns a
framed `RawMessage` into a `BackendMsg`; a decode failure means the stream is
not speaking protocol 3 and the connection must be considered poisoned (the
machine layer enforces that).
-/

/-- Backend transaction status from `ReadyForQuery`. -/
inductive TxStatus where
  | idle           -- 'I'
  | inTransaction  -- 'T'
  | failed         -- 'E': in a failed transaction block until ROLLBACK
  deriving Repr, BEq, Inhabited

/-- Error/notice fields as raw `(code, value)` pairs in wire order (codes from
protocol §53.8: S/V/C/M/D/H/P/p/q/W/s/t/c/d/n/F/L/R). Kept raw so nothing is
lost; accessors decode the common ones. -/
structure ErrorFields where
  fields : Array (UInt8 × String)
  deriving Repr, BEq, Inhabited

namespace ErrorFields

def find? (e : ErrorFields) (code : Char) : Option String :=
  (e.fields.find? (fun p => p.1 == UInt8.ofNat code.toNat)).map (·.2)

def severity? (e : ErrorFields) : Option String := e.find? 'S'
/-- Nonlocalized severity (always ERROR/FATAL/PANIC/WARNING/...). -/
def severityCode? (e : ErrorFields) : Option String := e.find? 'V'
/-- SQLSTATE, e.g. "42P01". -/
def sqlState? (e : ErrorFields) : Option String := e.find? 'C'
def message? (e : ErrorFields) : Option String := e.find? 'M'
def detail? (e : ErrorFields) : Option String := e.find? 'D'
def hint? (e : ErrorFields) : Option String := e.find? 'H'
/-- 1-based character index into the query string. -/
def position? (e : ErrorFields) : Option Nat := (e.find? 'P').bind String.toNat?
def internalPosition? (e : ErrorFields) : Option Nat := (e.find? 'p').bind String.toNat?
def internalQuery? (e : ErrorFields) : Option String := e.find? 'q'
def context? (e : ErrorFields) : Option String := e.find? 'W'
def schemaName? (e : ErrorFields) : Option String := e.find? 's'
def tableName? (e : ErrorFields) : Option String := e.find? 't'
def columnName? (e : ErrorFields) : Option String := e.find? 'c'
def dataTypeName? (e : ErrorFields) : Option String := e.find? 'd'
def constraintName? (e : ErrorFields) : Option String := e.find? 'n'
def sourceFile? (e : ErrorFields) : Option String := e.find? 'F'
def sourceLine? (e : ErrorFields) : Option String := e.find? 'L'
def sourceRoutine? (e : ErrorFields) : Option String := e.find? 'R'

end ErrorFields

/-- One column of a `RowDescription`. -/
structure ColumnDesc where
  name : String
  /-- Originating table OID, or 0. -/
  tableOid : UInt32
  /-- Originating column attribute number, or 0. -/
  attnum : UInt16
  typeOid : UInt32
  /-- pg_type.typlen; negative means variable length. -/
  typeSize : Int16
  typeMod : Int32
  /-- 0 = text, 1 = binary. -/
  format : UInt16
  deriving Repr, BEq, Inhabited

/-- Authentication request subtypes ('R' messages). -/
inductive AuthRequest where
  | ok
  | kerberosV5
  | cleartextPassword
  | md5Password (salt : ByteArray)
  | gss
  | gssContinue (data : ByteArray)
  | sspi
  | sasl (mechanisms : Array String)
  | saslContinue (data : ByteArray)
  | saslFinal (data : ByteArray)
  | unknown (code : UInt32)
  deriving Repr, BEq, Inhabited

inductive BackendMsg where
  | auth (request : AuthRequest)
  | backendKeyData (processId : UInt32) (secret : ByteArray)
  | bindComplete
  | closeComplete
  | commandComplete (tag : String)
  | copyData (data : ByteArray)
  | copyDone
  | copyInResponse (overallFormat : UInt8) (columnFormats : Array UInt16)
  | copyOutResponse (overallFormat : UInt8) (columnFormats : Array UInt16)
  | copyBothResponse (overallFormat : UInt8) (columnFormats : Array UInt16)
  | dataRow (columns : Array (Option ByteArray))
  | emptyQueryResponse
  | errorResponse (fields : ErrorFields)
  | functionCallResponse (result : Option ByteArray)
  | negotiateProtocolVersion (minorVersion : UInt32) (unrecognizedOptions : Array String)
  | noData
  | noticeResponse (fields : ErrorFields)
  | notificationResponse (processId : UInt32) (channel : String) (payload : String)
  | parameterDescription (typeOids : Array UInt32)
  | parameterStatus (name : String) (value : String)
  | parseComplete
  | portalSuspended
  | readyForQuery (status : TxStatus)
  | rowDescription (columns : Array ColumnDesc)
  deriving Repr, BEq, Inhabited

/-- Sequential reader over a message payload. -/
structure Reader where
  bytes : ByteArray
  off : Nat := 0
  deriving Inhabited

namespace Reader

def ofPayload (payload : ByteArray) : Reader := { bytes := payload }

def remaining (r : Reader) : Nat := r.bytes.size - r.off

def atEnd (r : Reader) : Bool := r.off ≥ r.bytes.size

def u8? (r : Reader) : Option (UInt8 × Reader) :=
  if r.off < r.bytes.size then
    some (r.bytes.get! r.off, { r with off := r.off + 1 })
  else none

def u16? (r : Reader) : Option (UInt16 × Reader) :=
  (getUInt16? r.bytes r.off).map ((·, { r with off := r.off + 2 }))

def u32? (r : Reader) : Option (UInt32 × Reader) :=
  (getUInt32? r.bytes r.off).map ((·, { r with off := r.off + 4 }))

def i32? (r : Reader) : Option (Int32 × Reader) :=
  (r.u32?).map (fun (v, r') => (v.toInt32, r'))

def cstring? (r : Reader) : Option (String × Reader) :=
  (getCString? r.bytes r.off).map (fun (s, n) => (s, { r with off := n }))

def take? (r : Reader) (n : Nat) : Option (ByteArray × Reader) :=
  if r.off + n ≤ r.bytes.size then
    some (r.bytes.extract r.off (r.off + n), { r with off := r.off + n })
  else none

def rest (r : Reader) : ByteArray × Reader :=
  (r.bytes.extract r.off r.bytes.size, { r with off := r.bytes.size })

end Reader

namespace Backend

private abbrev DecodeM := StateT Reader (Except String)

private def lift? (what : String) (f : Reader → Option (α × Reader)) : DecodeM α := do
  match f (← get) with
  | some (v, r) => set r; pure v
  | none => throw s!"truncated {what}"

private def ru8 (what : String := "byte") : DecodeM UInt8 := lift? what Reader.u8?
private def ru16 (what : String := "int16") : DecodeM UInt16 := lift? what Reader.u16?
private def ru32 (what : String := "int32") : DecodeM UInt32 := lift? what Reader.u32?
private def ri32 (what : String := "int32") : DecodeM Int32 := lift? what Reader.i32?
private def rcstring (what : String := "string") : DecodeM String := lift? what Reader.cstring?
private def rtake (n : Nat) (what : String := "bytes") : DecodeM ByteArray :=
  lift? what (Reader.take? · n)
private def rrest : DecodeM ByteArray := do
  let (bytes, r) := (← get).rest
  set r
  pure bytes

/-- Payload fully consumed; anything left means a framing/desync bug. -/
private def rdone (what : String) : DecodeM Unit := do
  let r ← get
  unless r.atEnd do throw s!"{what}: {r.remaining} trailing bytes"

private def rcount (n : Nat) (item : DecodeM α) : DecodeM (Array α) := do
  let mut out := Array.empty
  for _ in [0:n] do
    out := out.push (← item)
  pure out

private def authRequest : DecodeM AuthRequest := do
  match (← ru32 "auth code").toNat with
  | 0 => pure .ok
  | 2 => pure .kerberosV5
  | 3 => pure .cleartextPassword
  | 5 => pure (.md5Password (← rtake 4 "md5 salt"))
  | 7 => pure .gss
  | 8 => pure (.gssContinue (← rrest))
  | 9 => pure .sspi
  | 10 =>
    let mut mechanisms := Array.empty
    let mut done := false
    while !done do
      let r ← get
      if r.atEnd then
        throw "truncated SASL mechanism list"
      else if r.bytes.get! r.off == 0 then
        set { r with off := r.off + 1 }
        done := true
      else
        mechanisms := mechanisms.push (← rcstring "SASL mechanism")
    pure (.sasl mechanisms)
  | 11 => pure (.saslContinue (← rrest))
  | 12 => pure (.saslFinal (← rrest))
  | code => pure (.unknown (UInt32.ofNat code))

private def copyResponse : DecodeM (UInt8 × Array UInt16) := do
  let overall ← ru8 "copy format"
  let n ← ru16 "copy column count"
  let formats ← rcount n.toNat (ru16 "copy column format")
  pure (overall, formats)

private def errorFields : DecodeM ErrorFields := do
  let mut fields := Array.empty
  let mut done := false
  while !done do
    let code ← ru8 "field code"
    if code == 0 then
      done := true
    else
      fields := fields.push (code, ← rcstring "field value")
  pure { fields }

private def column : DecodeM ColumnDesc := do
  let name ← rcstring "column name"
  let tableOid ← ru32 "table oid"
  let attnum ← ru16 "attnum"
  let typeOid ← ru32 "type oid"
  let typeSize := (← ru16 "type size").toInt16
  let typeMod := (← ru32 "type modifier").toInt32
  let format ← ru16 "format code"
  pure { name, tableOid, attnum, typeOid, typeSize, typeMod, format }

private def body (tag : BackendTag) : DecodeM BackendMsg := do
  match tag with
  | .authentication => pure (.auth (← authRequest))
  | .backendKeyData =>
    let pid ← ru32 "backend pid"
    let secret ← rrest
    if secret.size == 0 || secret.size > 256 then
      throw s!"cancel key length {secret.size} out of range"
    pure (.backendKeyData pid secret)
  | .bindComplete => pure .bindComplete
  | .closeComplete => pure .closeComplete
  | .commandComplete => pure (.commandComplete (← rcstring "command tag"))
  | .copyData => pure (.copyData (← rrest))
  | .copyDone => pure .copyDone
  | .copyInResponse =>
    let (overall, formats) ← copyResponse
    pure (.copyInResponse overall formats)
  | .copyOutResponse =>
    let (overall, formats) ← copyResponse
    pure (.copyOutResponse overall formats)
  | .copyBothResponse =>
    let (overall, formats) ← copyResponse
    pure (.copyBothResponse overall formats)
  | .dataRow =>
    let n ← ru16 "column count"
    let columns ← rcount n.toNat do
      let len ← ri32 "column length"
      if len == -1 then
        pure none
      else if len < 0 then
        throw s!"negative column length {len}"
      else
        some <$> rtake len.toInt.toNat "column value"
    pure (.dataRow columns)
  | .emptyQueryResponse => pure .emptyQueryResponse
  | .errorResponse => pure (.errorResponse (← errorFields))
  | .functionCallResponse =>
    let len ← ri32 "result length"
    if len == -1 then
      pure (.functionCallResponse none)
    else if len < 0 then
      throw s!"negative result length {len}"
    else
      pure (.functionCallResponse (some (← rtake len.toInt.toNat "result value")))
  | .negotiateProtocolVersion =>
    let minor ← ru32 "minor version"
    let n ← ru32 "option count"
    let options ← rcount n.toNat (rcstring "option name")
    pure (.negotiateProtocolVersion minor options)
  | .noData => pure .noData
  | .noticeResponse => pure (.noticeResponse (← errorFields))
  | .notificationResponse =>
    let pid ← ru32 "notifying pid"
    let channel ← rcstring "channel"
    let payload ← rcstring "payload"
    pure (.notificationResponse pid channel payload)
  | .parameterDescription =>
    let n ← ru16 "parameter count"
    pure (.parameterDescription (← rcount n.toNat (ru32 "parameter oid")))
  | .parameterStatus =>
    let name ← rcstring "parameter name"
    pure (.parameterStatus name (← rcstring "parameter value"))
  | .parseComplete => pure .parseComplete
  | .portalSuspended => pure .portalSuspended
  | .readyForQuery =>
    match (← ru8 "transaction status") with
    | 73 => pure (.readyForQuery .idle)           -- 'I'
    | 84 => pure (.readyForQuery .inTransaction)  -- 'T'
    | 69 => pure (.readyForQuery .failed)         -- 'E'
    | other => throw s!"unknown transaction status {other}"
  | .rowDescription =>
    let n ← ru16 "field count"
    pure (.rowDescription (← rcount n.toNat column))
  | .unknown value => throw s!"unknown backend message tag {value}"

def decode (msg : RawMessage) : Except String BackendMsg := do
  let tag := BackendTag.ofUInt8 msg.tag
  let (result, r) ← (body tag).run (Reader.ofPayload msg.payload)
  -- CopyData aside (raw passthrough), every message must consume its payload
  unless r.atEnd do
    throw s!"{repr tag}: {r.remaining} trailing bytes"
  pure result

end Backend

end Protocol
end Pg
