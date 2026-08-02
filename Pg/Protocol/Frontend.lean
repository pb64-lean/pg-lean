module

public import Pg.Protocol.Message

public section

namespace Pg
namespace Protocol
namespace Frontend

/-!
Typed frontend message encoders (post-startup, tagged). Startup-phase
encoders (`encodeStartup`, `encodeSSLRequest`, `encodeCancelRequest`) live in
`Message.lean` since they share the untagged framing.
-/

/-- `Parse`: named (or unnamed, `""`) prepared statement from SQL, with
optional parameter-type OIDs (0 or absent = infer). -/
def parse (name query : String) (paramTypeOids : Array UInt32 := #[]) : ByteArray :=
  let body := putCString (putCString ByteArray.empty name) query
  let body := putUInt16 body (UInt16.ofNat paramTypeOids.size)
  frame .parse (paramTypeOids.foldl putUInt32 body)

/-- `Bind`: create a portal from a prepared statement. `paramFormats` and
`resultFormats` follow the protocol's shorthand: empty = all text, one entry =
that format for everything, else one per parameter/column. `none` parameters
are NULL. -/
def bind (portal statement : String) (paramFormats : Array UInt16 := #[])
    (params : Array (Option ByteArray) := #[])
    (resultFormats : Array UInt16 := #[]) : ByteArray :=
  let body := putCString (putCString ByteArray.empty portal) statement
  let body := putUInt16 body (UInt16.ofNat paramFormats.size)
  let body := paramFormats.foldl putUInt16 body
  let body := putUInt16 body (UInt16.ofNat params.size)
  let body := params.foldl (fun acc p =>
    match p with
    | none => putInt32 acc (-1)
    | some value => putUInt32 acc (UInt32.ofNat value.size) ++ value) body
  let body := putUInt16 body (UInt16.ofNat resultFormats.size)
  frame .bind (resultFormats.foldl putUInt16 body)

def describeStatement (name : String) : ByteArray :=
  frame .describe (putCString (ByteArray.empty.push 83) name)  -- 'S'

def describePortal (name : String) : ByteArray :=
  frame .describe (putCString (ByteArray.empty.push 80) name)  -- 'P'

/-- `Execute`: run a portal; `maxRows = 0` means no limit, nonzero suspends
the portal after that many rows (`PortalSuspended`). -/
def execute (portal : String) (maxRows : UInt32 := 0) : ByteArray :=
  frame .execute (putUInt32 (putCString ByteArray.empty portal) maxRows)

def closeStatement (name : String) : ByteArray :=
  frame .close (putCString (ByteArray.empty.push 83) name)  -- 'S'

def closePortal (name : String) : ByteArray :=
  frame .close (putCString (ByteArray.empty.push 80) name)  -- 'P'

def flush : ByteArray := frame .flush

def sync : ByteArray := frame .sync

/-- Cleartext or md5 password response (auth phase). -/
def password (secret : String) : ByteArray :=
  frame .password (putCString ByteArray.empty secret)

/-- `SASLInitialResponse`: mechanism name plus the initial client response. -/
def saslInitialResponse (mechanism : String) (initial : ByteArray) : ByteArray :=
  let body := putCString ByteArray.empty mechanism
  let body := putUInt32 body (UInt32.ofNat initial.size)
  frame .password (body ++ initial)

/-- `SASLResponse`: continuation data, raw (no length prefix of its own). -/
def saslResponse (data : ByteArray) : ByteArray :=
  frame .password data

def copyData (data : ByteArray) : ByteArray :=
  frame .copyData data

def copyDone : ByteArray := frame .copyDone

def copyFail (reason : String) : ByteArray :=
  frame .copyFail (putCString ByteArray.empty reason)

end Frontend
end Protocol
end Pg
