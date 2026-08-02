module

public section

namespace Pg
namespace Protocol

/-!
PostgreSQL frontend/backend wire protocol, version 3.0: byte-level message
framing. Every message after the startup phase is `tag (1 byte)` followed by a
big-endian `Int32` length that counts itself and the payload (but not the tag).
Startup-phase frontend messages (StartupMessage, SSLRequest, CancelRequest)
omit the tag byte.

This layer deals only in raw framed messages (`RawMessage`) and incremental
decoding of a TCP byte stream (`DecodeState`); typed message
encoding/decoding builds on top of it.
-/

def protocolVersion : UInt32 := 196608  -- 3.0

/-- Protocol 3.2 (PostgreSQL 18+): variable-length cancel keys. 3.1 was never
used (skipped due to a pgbouncer negotiation bug). -/
def protocolVersion32 : UInt32 := 196610

def sslRequestCode : UInt32 := 80877103

def cancelRequestCode : UInt32 := 80877102

/-- Length prefix counts itself (4 bytes) but not the tag byte. -/
def lengthFieldSize : Nat := 4

/-- Sanity cap on a single message body; PostgreSQL itself enforces ~1 GiB. -/
def maxMessageLength : Nat := 1 <<< 30

-- Big-endian primitive writers, appending to an accumulator ByteArray.

def putUInt16 (out : ByteArray) (v : UInt16) : ByteArray :=
  (out.push (v >>> 8).toUInt8).push v.toUInt8

def putUInt32 (out : ByteArray) (v : UInt32) : ByteArray :=
  let out := out.push (v >>> 24).toUInt8
  let out := out.push (v >>> 16).toUInt8
  let out := out.push (v >>> 8).toUInt8
  out.push v.toUInt8

def putInt32 (out : ByteArray) (v : Int32) : ByteArray :=
  putUInt32 out v.toUInt32

/-- Null-terminated string, the protocol's only string representation. -/
def putCString (out : ByteArray) (s : String) : ByteArray :=
  (out ++ s.toUTF8).push 0

-- Big-endian primitive readers over a ByteArray at an offset. Bounds are the
-- caller's responsibility only in the sense that failures are `none`.

def getUInt16? (bytes : ByteArray) (off : Nat) : Option UInt16 :=
  if off + 2 ≤ bytes.size then
    some ((bytes.get! off).toUInt16 <<< 8 ||| (bytes.get! (off + 1)).toUInt16)
  else none

def getUInt32? (bytes : ByteArray) (off : Nat) : Option UInt32 :=
  if off + 4 ≤ bytes.size then
    some <|
      (bytes.get! off).toUInt32 <<< 24 |||
      (bytes.get! (off + 1)).toUInt32 <<< 16 |||
      (bytes.get! (off + 2)).toUInt32 <<< 8 |||
      (bytes.get! (off + 3)).toUInt32
  else none

def getInt32? (bytes : ByteArray) (off : Nat) : Option Int32 :=
  (getUInt32? bytes off).map (·.toInt32)

/-- Reads a null-terminated UTF-8 string starting at `off`; returns the string
and the offset just past the terminator. -/
def getCString? (bytes : ByteArray) (off : Nat) : Option (String × Nat) := do
  let rec findNul (i : Nat) : Option Nat :=
    if h : i < bytes.size then
      if bytes.get! i == 0 then some i else findNul (i + 1)
    else none
  termination_by bytes.size - i
  let nul ← findNul off
  let s ← String.fromUTF8? (bytes.extract off nul)
  pure (s, nul + 1)

/-- A framed protocol message: one tag byte plus the length-delimited payload
(the payload excludes the length field itself). -/
structure RawMessage where
  tag : UInt8
  payload : ByteArray := ByteArray.empty
  deriving Inhabited

namespace RawMessage

def encode (msg : RawMessage) : ByteArray :=
  let out := ByteArray.empty.push msg.tag
  let out := putUInt32 out (msg.payload.size + lengthFieldSize).toUInt32
  out ++ msg.payload

end RawMessage

/-- Startup-phase messages carry no tag: just `length (incl. itself) ++ payload`. -/
def encodeUntagged (payload : ByteArray) : ByteArray :=
  putUInt32 ByteArray.empty (payload.size + lengthFieldSize).toUInt32 ++ payload

/-- The StartupMessage: protocol version then `key\0value\0` pairs and a final
terminator byte. -/
def encodeStartup (params : Array (String × String))
    (version : UInt32 := protocolVersion) : ByteArray :=
  let body := putUInt32 ByteArray.empty version
  let body := params.foldl (fun acc (kv : String × String) =>
    putCString (putCString acc kv.1) kv.2) body
  encodeUntagged (body.push 0)

def encodeSSLRequest : ByteArray :=
  encodeUntagged (putUInt32 ByteArray.empty sslRequestCode)

/-- The secret key is 4 bytes under protocol 3.0 and variable-length (≤ 256
bytes) under 3.2; either way the wire format is `code ++ pid ++ secret`. -/
def encodeCancelRequest (processId : UInt32) (secretKey : ByteArray) : ByteArray :=
  encodeUntagged
    (putUInt32 (putUInt32 ByteArray.empty cancelRequestCode) processId ++ secretKey)

/-- Incremental decoder for the (tagged) message stream a client receives from
the backend. Feed TCP chunks with `decodeChunk`; complete messages accumulate
in `messages`. -/
structure DecodeState where
  buffered : ByteArray := ByteArray.empty
  messages : Array RawMessage := #[]
  deriving Inhabited

private partial def parseBuffered (buffered : ByteArray) (messages : Array RawMessage) :
    Except String DecodeState := do
  if buffered.size < 1 + lengthFieldSize then
    pure { buffered, messages }
  else
    let tag := buffered.get! 0
    let some len32 := getUInt32? buffered 1
      | pure { buffered, messages }
    let len := len32.toNat
    if len < lengthFieldSize || len > maxMessageLength then
      throw s!"invalid message length {len} (tag {tag})"
    let endPos := 1 + len
    if buffered.size < endPos then
      pure { buffered, messages }
    else
      let payload := buffered.extract (1 + lengthFieldSize) endPos
      let rest := buffered.extract endPos buffered.size
      parseBuffered rest (messages.push { tag, payload })

def DecodeState.feed (state : DecodeState) (chunk : ByteArray) :
    Except String DecodeState :=
  parseBuffered (state.buffered ++ chunk) state.messages

/-- Drains completed messages, keeping any partial trailing bytes buffered. -/
def DecodeState.take (state : DecodeState) : Array RawMessage × DecodeState :=
  (state.messages, { state with messages := #[] })

/-- Backend message tags a client must recognize (protocol 3.0). -/
inductive BackendTag where
  | authentication          -- 'R'
  | backendKeyData          -- 'K'
  | bindComplete            -- '2'
  | closeComplete           -- '3'
  | commandComplete         -- 'C'
  | copyData                -- 'd'
  | copyDone                -- 'c'
  | copyInResponse          -- 'G'
  | copyOutResponse         -- 'H'
  | copyBothResponse        -- 'W'
  | dataRow                 -- 'D'
  | emptyQueryResponse      -- 'I'
  | errorResponse           -- 'E'
  | functionCallResponse    -- 'V'
  | negotiateProtocolVersion -- 'v'
  | noData                  -- 'n'
  | noticeResponse          -- 'N'
  | notificationResponse    -- 'A'
  | parameterDescription    -- 't'
  | parameterStatus         -- 'S'
  | parseComplete           -- '1'
  | portalSuspended         -- 's'
  | readyForQuery           -- 'Z'
  | rowDescription          -- 'T'
  | unknown (value : UInt8)
  deriving Inhabited, Repr, DecidableEq

namespace BackendTag

def ofUInt8 : UInt8 → BackendTag
  | 82 => .authentication
  | 75 => .backendKeyData
  | 50 => .bindComplete
  | 51 => .closeComplete
  | 67 => .commandComplete
  | 100 => .copyData
  | 99 => .copyDone
  | 71 => .copyInResponse
  | 72 => .copyOutResponse
  | 87 => .copyBothResponse
  | 68 => .dataRow
  | 73 => .emptyQueryResponse
  | 69 => .errorResponse
  | 86 => .functionCallResponse
  | 118 => .negotiateProtocolVersion
  | 110 => .noData
  | 78 => .noticeResponse
  | 65 => .notificationResponse
  | 116 => .parameterDescription
  | 83 => .parameterStatus
  | 49 => .parseComplete
  | 115 => .portalSuspended
  | 90 => .readyForQuery
  | 84 => .rowDescription
  | value => .unknown value

def toUInt8 : BackendTag → UInt8
  | .authentication => 82
  | .backendKeyData => 75
  | .bindComplete => 50
  | .closeComplete => 51
  | .commandComplete => 67
  | .copyData => 100
  | .copyDone => 99
  | .copyInResponse => 71
  | .copyOutResponse => 72
  | .copyBothResponse => 87
  | .dataRow => 68
  | .emptyQueryResponse => 73
  | .errorResponse => 69
  | .functionCallResponse => 86
  | .negotiateProtocolVersion => 118
  | .noData => 110
  | .noticeResponse => 78
  | .notificationResponse => 65
  | .parameterDescription => 116
  | .parameterStatus => 83
  | .parseComplete => 49
  | .portalSuspended => 115
  | .readyForQuery => 90
  | .rowDescription => 84
  | .unknown value => value

end BackendTag

/-- Frontend message tags (post-startup). -/
inductive FrontendTag where
  | bind          -- 'B'
  | close         -- 'C'
  | copyData      -- 'd'
  | copyDone      -- 'c'
  | copyFail      -- 'f'
  | describe      -- 'D'
  | execute       -- 'E'
  | flush         -- 'H'
  | functionCall  -- 'F'
  | parse         -- 'P'
  | password      -- 'p' (also SASL/GSS responses)
  | query         -- 'Q'
  | sync          -- 'S'
  | terminate     -- 'X'
  deriving Inhabited, Repr, DecidableEq

namespace FrontendTag

def toUInt8 : FrontendTag → UInt8
  | .bind => 66
  | .close => 67
  | .copyData => 100
  | .copyDone => 99
  | .copyFail => 102
  | .describe => 68
  | .execute => 69
  | .flush => 72
  | .functionCall => 70
  | .parse => 80
  | .password => 112
  | .query => 81
  | .sync => 83
  | .terminate => 88

end FrontendTag

/-- Convenience: frame a frontend message from its typed tag. -/
def frame (tag : FrontendTag) (payload : ByteArray := ByteArray.empty) : ByteArray :=
  RawMessage.encode { tag := tag.toUInt8, payload }

/-- The simple-query message: `Q` + SQL as cstring. -/
def encodeQuery (sql : String) : ByteArray :=
  frame .query (putCString ByteArray.empty sql)

def encodeTerminate : ByteArray :=
  frame .terminate

end Protocol
end Pg
