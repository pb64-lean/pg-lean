module

public import Pg.Protocol.Message
public import Pg.Protocol.Backend

public section

namespace Pg
namespace TestSupport
namespace Be

open Pg.Protocol

/-!
Backend-message *builders* — encoders for messages only a server sends,
used to author test exchanges. Test-only by design: the library itself ships
only backend decoders. The chain of trust is anchored in WireTest, which pins
each builder against a hand-frozen hex golden before flows rely on them.
-/

def msg (tag : UInt8) (body : ByteArray := ByteArray.empty) : ByteArray :=
  RawMessage.encode { tag, payload := body }

def authOk : ByteArray := msg 82 (putUInt32 ByteArray.empty 0)
def authKerberos : ByteArray := msg 82 (putUInt32 ByteArray.empty 2)
def authCleartext : ByteArray := msg 82 (putUInt32 ByteArray.empty 3)
def authMd5 (salt : ByteArray) : ByteArray := msg 82 (putUInt32 ByteArray.empty 5 ++ salt)
def authSasl (mechanisms : Array String) : ByteArray :=
  msg 82 ((mechanisms.foldl putCString (putUInt32 ByteArray.empty 10)).push 0)
def authSaslContinue (data : String) : ByteArray :=
  msg 82 (putUInt32 ByteArray.empty 11 ++ data.toUTF8)
def authSaslFinal (data : String) : ByteArray :=
  msg 82 (putUInt32 ByteArray.empty 12 ++ data.toUTF8)

def backendKeyData (processId : UInt32) (secret : ByteArray) : ByteArray :=
  msg 75 (putUInt32 ByteArray.empty processId ++ secret)

def parameterStatus (name value : String) : ByteArray :=
  msg 83 (putCString (putCString ByteArray.empty name) value)

def readyForQuery (status : Char) : ByteArray :=
  msg 90 (ByteArray.empty.push (UInt8.ofNat status.toNat))

def parseComplete : ByteArray := msg 49
def bindComplete : ByteArray := msg 50
def closeComplete : ByteArray := msg 51
def noData : ByteArray := msg 110
def portalSuspended : ByteArray := msg 115
def emptyQueryResponse : ByteArray := msg 73
def copyDone : ByteArray := msg 99

def commandComplete (tag : String) : ByteArray :=
  msg 67 (putCString ByteArray.empty tag)

def dataRow (columns : Array (Option ByteArray)) : ByteArray := Id.run do
  let mut body := putUInt16 ByteArray.empty (UInt16.ofNat columns.size)
  for col in columns do
    match col with
    | none => body := putInt32 body (-1)
    | some value => body := putUInt32 body (UInt32.ofNat value.size) ++ value
  return msg 68 body

/-- Text-column shorthand: `row #["1", "x"]`. -/
def row (columns : Array String) : ByteArray :=
  dataRow (columns.map (fun s => some s.toUTF8))

def rowDescription (columns : Array ColumnDesc) : ByteArray := Id.run do
  let mut body := putUInt16 ByteArray.empty (UInt16.ofNat columns.size)
  for c in columns do
    body := putCString body c.name
    body := putUInt32 body c.tableOid
    body := putUInt16 body c.attnum
    body := putUInt32 body c.typeOid
    body := putUInt16 body c.typeSize.toUInt16
    body := putUInt32 body c.typeMod.toUInt32
    body := putUInt16 body c.format
  return msg 84 body

/-- Minimal column: name + type OID, everything else defaulted like a
computed column (table 0, attnum 0, varlena, text format). -/
def col (name : String) (typeOid : UInt32 := 25) : ColumnDesc :=
  { name, tableOid := 0, attnum := 0, typeOid, typeSize := -1, typeMod := -1, format := 0 }

def errorFieldsBody (pairs : Array (Char × String)) : ByteArray :=
  (pairs.foldl (fun acc (p : Char × String) =>
    putCString (acc.push (UInt8.ofNat p.1.toNat)) p.2) ByteArray.empty).push 0

/-- Standard three-field server error (severity, SQLSTATE, message). -/
def errorResponse (severity code message : String) : ByteArray :=
  msg 69 (errorFieldsBody #[('S', severity), ('C', code), ('M', message)])

def errorResponseFields (pairs : Array (Char × String)) : ByteArray :=
  msg 69 (errorFieldsBody pairs)

def noticeResponse (severity code message : String) : ByteArray :=
  msg 78 (errorFieldsBody #[('S', severity), ('C', code), ('M', message)])

def notification (processId : UInt32) (channel payload : String) : ByteArray :=
  msg 65 (putCString (putCString (putUInt32 ByteArray.empty processId) channel) payload)

def parameterDescription (typeOids : Array UInt32) : ByteArray :=
  msg 116 (typeOids.foldl putUInt32 (putUInt16 ByteArray.empty (UInt16.ofNat typeOids.size)))

def copyInResponse (overallFormat : UInt8 := 0) (columnFormats : Array UInt16 := #[]) : ByteArray :=
  msg 71 (columnFormats.foldl putUInt16
    (putUInt16 (ByteArray.empty.push overallFormat) (UInt16.ofNat columnFormats.size)))

def copyOutResponse (overallFormat : UInt8 := 0) (columnFormats : Array UInt16 := #[]) : ByteArray :=
  msg 72 (columnFormats.foldl putUInt16
    (putUInt16 (ByteArray.empty.push overallFormat) (UInt16.ofNat columnFormats.size)))

def copyBothResponse (overallFormat : UInt8 := 0) (columnFormats : Array UInt16 := #[]) : ByteArray :=
  msg 87 (columnFormats.foldl putUInt16
    (putUInt16 (ByteArray.empty.push overallFormat) (UInt16.ofNat columnFormats.size)))

def copyData (data : ByteArray) : ByteArray := msg 100 data

def negotiateProtocolVersion (minorVersion : UInt32) (unrecognized : Array String := #[]) : ByteArray :=
  msg 118 (unrecognized.foldl putCString
    (putUInt32 (putUInt32 ByteArray.empty minorVersion) (UInt32.ofNat unrecognized.size)))

end Be
end TestSupport
end Pg
