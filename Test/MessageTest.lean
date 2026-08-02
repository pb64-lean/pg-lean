import Pg.Protocol.Message

open Pg.Protocol

def expect (cond : Bool) (msg : String) : IO Unit := do
  unless cond do throw (IO.userError msg)

def main : IO Unit := do
  -- primitive roundtrips
  let bytes := putUInt32 (putUInt16 ByteArray.empty 0xBEEF) 0xDEADBEEF
  expect (getUInt16? bytes 0 == some 0xBEEF) "u16 roundtrip"
  expect (getUInt32? bytes 2 == some 0xDEADBEEF) "u32 roundtrip"
  expect (getUInt32? bytes 3 == none) "u32 out of bounds"
  let cs := putCString ByteArray.empty "hello"
  expect (getCString? cs 0 == some ("hello", 6)) "cstring roundtrip"
  expect (getCString? (ByteArray.mk #[104, 105]) 0 == none) "cstring missing nul"

  -- startup message golden: 3.0 version, one param, terminator
  let startup := encodeStartup #[("user", "bill")]
  expect (getUInt32? startup 0 == some startup.size.toUInt32) "startup length prefix"
  expect (getUInt32? startup 4 == some protocolVersion) "startup version"
  expect (startup.get! (startup.size - 1) == 0) "startup terminator"
  expect (getCString? startup 8 == some ("user", 13)) "startup param key"

  -- tagged framing roundtrip through the incremental decoder, split mid-message
  let q := encodeQuery "SELECT 1"
  let t := encodeTerminate
  let stream := q ++ t
  let half := stream.extract 0 7
  let rest := stream.extract 7 stream.size
  let st ← IO.ofExcept ((({} : DecodeState).feed half))
  expect (st.messages.isEmpty) "no message from partial chunk"
  let st ← IO.ofExcept (st.feed rest)
  let (msgs, st) := st.take
  expect (msgs.size == 2) s!"two messages, got {msgs.size}"
  expect (st.buffered.isEmpty) "no residual bytes"
  expect (msgs[0]!.tag == FrontendTag.query.toUInt8) "query tag"
  expect (getCString? msgs[0]!.payload 0 == some ("SELECT 1", 9)) "query payload"
  expect (msgs[1]!.tag == FrontendTag.terminate.toUInt8) "terminate tag"
  expect (msgs[1]!.payload.isEmpty) "terminate empty payload"

  -- backend tag mapping is a bijection on known tags
  expect (BackendTag.ofUInt8 90 == .readyForQuery) "Z tag"
  expect ((BackendTag.ofUInt8 (BackendTag.errorResponse.toUInt8)) == .errorResponse) "tag roundtrip"
  expect (BackendTag.ofUInt8 33 == .unknown 33) "unknown tag"

  -- corrupt length is rejected
  let bad := ByteArray.mk #[90, 0, 0, 0, 1]
  match ({} : DecodeState).feed bad with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError "expected invalid-length error")

  IO.println "all pg protocol assertions passed"
