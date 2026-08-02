import Pg.Protocol.Message
import Pg.Protocol.Backend
import Pg.Protocol.Frontend
import Test.Support.Hex
import Test.Support.Backend

/-!
Wire-format goldens for the typed message catalog.

Chain of trust: frontend encoders and the test-support backend builders are
pinned against hand-frozen hex literals (derived from protocol §53.7); the
backend decoder is then asserted against the builders' bytes. Flow tests can
therefore use builders freely without re-proving byte layouts.
-/

open Pg.Protocol
open Pg.TestSupport
open Pg.TestSupport.Be

def expect (cond : Bool) (msg : String) : IO Unit := do
  unless cond do throw (IO.userError msg)

def expectEq [BEq α] [Repr α] (got want : α) (label : String) : IO Unit := do
  unless got == want do
    throw (IO.userError s!"{label}: got {repr got}, want {repr want}")

def expectBytes (got want : ByteArray) (label : String) : IO Unit := do
  unless got == want do
    throw (IO.userError s!"{label}:\n  got  {hexDump got}\n  want {hexDump want}")

/-- Split a byte stream into RawMessages, expecting exactly `n`. -/
def parseAll (bytes : ByteArray) (n : Nat) (label : String) : IO (Array RawMessage) := do
  let st ← IO.ofExcept (({} : DecodeState).feed bytes)
  let (msgs, st) := st.take
  expect st.buffered.isEmpty s!"{label}: residual bytes"
  expect (msgs.size == n) s!"{label}: {msgs.size} messages, want {n}"
  pure msgs

def decodeOne (bytes : ByteArray) (label : String) : IO BackendMsg := do
  let msgs ← parseAll bytes 1 label
  IO.ofExcept (Backend.decode msgs[0]!)

def expectDecode (bytes : ByteArray) (want : BackendMsg) (label : String) : IO Unit := do
  expectEq (← decodeOne bytes label) want label

def expectDecodeError (payloadTag : UInt8) (payload : ByteArray) (label : String) : IO Unit := do
  match Backend.decode { tag := payloadTag, payload } with
  | .error _ => pure ()
  | .ok m => throw (IO.userError s!"{label}: expected decode error, got {repr m}")

def main : IO Unit := do
  -- ── frontend encoder goldens ────────────────────────────────────────────
  expectBytes Frontend.sync (hex "53 00 00 00 04") "sync"
  expectBytes Frontend.flush (hex "48 00 00 00 04") "flush"
  expectBytes encodeTerminate (hex "58 00 00 00 04") "terminate"
  expectBytes (encodeQuery "SELECT 1")
    (hex "51 00 00 00 0d" ++ ascii "SELECT 1" ++ hex "00") "query"
  expectBytes (Frontend.parse "s1" "SELECT 1")
    (hex "50 00 00 00 12" ++ ascii "s1" ++ hex "00" ++ ascii "SELECT 1" ++ hex "00 00 00")
    "parse"
  expectBytes (Frontend.bind "" "s1" #[] #[some (ascii "42")] #[])
    (hex "42 00 00 00 14 00" ++ ascii "s1" ++ hex "00 00 00 00 01 00 00 00 02" ++
      ascii "42" ++ hex "00 00")
    "bind"
  expectBytes (Frontend.bind "p" "s" #[1] #[none] #[1])
    (hex "42 00 00 00 16" ++ ascii "p" ++ hex "00" ++ ascii "s" ++
      hex "00 00 01 00 01 00 01 ff ff ff ff 00 01 00 01")
    "bind null + binary"
  expectBytes (Frontend.describeStatement "s1")
    (hex "44 00 00 00 08 53" ++ ascii "s1" ++ hex "00") "describe statement"
  expectBytes (Frontend.describePortal "")
    (hex "44 00 00 00 06 50 00") "describe portal"
  expectBytes (Frontend.execute "" 0)
    (hex "45 00 00 00 09 00 00 00 00 00") "execute"
  expectBytes (Frontend.execute "p" 50)
    (hex "45 00 00 00 0a" ++ ascii "p" ++ hex "00 00 00 00 32") "execute limited"
  expectBytes (Frontend.closeStatement "s1")
    (hex "43 00 00 00 08 53" ++ ascii "s1" ++ hex "00") "close statement"
  expectBytes (Frontend.closePortal "p")
    (hex "43 00 00 00 07 50" ++ ascii "p" ++ hex "00") "close portal"
  expectBytes (Frontend.password "md5abc")
    (hex "70 00 00 00 0b" ++ ascii "md5abc" ++ hex "00") "password"
  expectBytes (Frontend.saslInitialResponse "SCRAM-SHA-256" (ascii "n,,n=,r=x"))
    (hex "70 00 00 00 1f" ++ ascii "SCRAM-SHA-256" ++ hex "00 00 00 00 09" ++ ascii "n,,n=,r=x")
    "sasl initial"
  expectBytes (Frontend.saslResponse (ascii "c=biws"))
    (hex "70 00 00 00 0a" ++ ascii "c=biws") "sasl response"
  expectBytes (Frontend.copyData (ascii "1\tx\n"))
    (hex "64 00 00 00 08" ++ ascii "1\tx\n") "copy data"
  expectBytes Frontend.copyDone (hex "63 00 00 00 04") "copy done"
  expectBytes (Frontend.copyFail "nope")
    (hex "66 00 00 00 09" ++ ascii "nope" ++ hex "00") "copy fail"

  -- startup-phase goldens
  expectBytes (encodeStartup #[("user", "u")])
    (hex "00 00 00 10 00 03 00 00" ++ ascii "user" ++ hex "00" ++ ascii "u" ++ hex "00 00")
    "startup 3.0"
  expectBytes (encodeStartup #[("user", "u")] protocolVersion32)
    (hex "00 00 00 10 00 03 00 02" ++ ascii "user" ++ hex "00" ++ ascii "u" ++ hex "00 00")
    "startup 3.2"
  expectBytes encodeSSLRequest (hex "00 00 00 08 04 d2 16 2f") "ssl request"
  expectBytes (encodeCancelRequest 0x1234 (hex "00 01 02 03"))
    (hex "00 00 00 10 04 d2 16 2e 00 00 12 34 00 01 02 03") "cancel request"

  -- ── backend builder goldens (chain of trust for flow tests) ─────────────
  expectBytes authOk (hex "52 00 00 00 08 00 00 00 00") "authOk"
  expectBytes authCleartext (hex "52 00 00 00 08 00 00 00 03") "authCleartext"
  expectBytes (authMd5 (hex "01 02 03 04"))
    (hex "52 00 00 00 0c 00 00 00 05 01 02 03 04") "authMd5"
  expectBytes (authSasl #["SCRAM-SHA-256"])
    (hex "52 00 00 00 17 00 00 00 0a" ++ ascii "SCRAM-SHA-256" ++ hex "00 00") "authSasl"
  expectBytes (authSaslContinue "r=x")
    (hex "52 00 00 00 0b 00 00 00 0b" ++ ascii "r=x") "authSaslContinue"
  expectBytes (authSaslFinal "v=x")
    (hex "52 00 00 00 0b 00 00 00 0c" ++ ascii "v=x") "authSaslFinal"
  expectBytes (backendKeyData 1234 (hex "00 00 16 2e"))
    (hex "4b 00 00 00 0c 00 00 04 d2 00 00 16 2e") "backendKeyData"
  expectBytes (parameterStatus "client_encoding" "UTF8")
    (hex "53 00 00 00 19" ++ ascii "client_encoding" ++ hex "00" ++ ascii "UTF8" ++ hex "00")
    "parameterStatus"
  expectBytes (readyForQuery 'I') (hex "5a 00 00 00 05 49") "readyForQuery"
  expectBytes parseComplete (hex "31 00 00 00 04") "parseComplete"
  expectBytes bindComplete (hex "32 00 00 00 04") "bindComplete"
  expectBytes closeComplete (hex "33 00 00 00 04") "closeComplete"
  expectBytes noData (hex "6e 00 00 00 04") "noData"
  expectBytes portalSuspended (hex "73 00 00 00 04") "portalSuspended"
  expectBytes emptyQueryResponse (hex "49 00 00 00 04") "emptyQueryResponse"
  expectBytes (commandComplete "SELECT 1")
    (hex "43 00 00 00 0d" ++ ascii "SELECT 1" ++ hex "00") "commandComplete"
  expectBytes (dataRow #[some (ascii "42"), none])
    (hex "44 00 00 00 10 00 02 00 00 00 02" ++ ascii "42" ++ hex "ff ff ff ff") "dataRow"
  expectBytes (rowDescription #[col "a" 23])
    (hex "54 00 00 00 1a 00 01" ++ ascii "a" ++
      hex "00 00 00 00 00 00 00 00 00 00 17 ff ff ff ff ff ff 00 00")
    "rowDescription"
  expectBytes (errorResponse "ERROR" "42P01" "boom")
    (hex "45 00 00 00 19 53" ++ ascii "ERROR" ++ hex "00 43" ++ ascii "42P01" ++
      hex "00 4d" ++ ascii "boom" ++ hex "00 00")
    "errorResponse"
  expectBytes (notification 77 "chan" "hi")
    (hex "41 00 00 00 10 00 00 00 4d" ++ ascii "chan" ++ hex "00" ++ ascii "hi" ++ hex "00")
    "notification"
  expectBytes (parameterDescription #[23, 25])
    (hex "74 00 00 00 0e 00 02 00 00 00 17 00 00 00 19") "parameterDescription"
  expectBytes (copyInResponse 0 #[0, 0])
    (hex "47 00 00 00 0b 00 00 02 00 00 00 00") "copyInResponse"
  expectBytes (copyOutResponse 1 #[1])
    (hex "48 00 00 00 09 01 00 01 00 01") "copyOutResponse"
  expectBytes (copyData (ascii "x"))
    (hex "64 00 00 00 05" ++ ascii "x") "be copyData"
  expectBytes copyDone (hex "63 00 00 00 04") "be copyDone"
  expectBytes (negotiateProtocolVersion 0 #["_pq_.x"])
    (hex "76 00 00 00 13 00 00 00 00 00 00 00 01" ++ ascii "_pq_.x" ++ hex "00")
    "negotiateProtocolVersion"

  -- ── decoder against the pinned builders ─────────────────────────────────
  expectDecode authOk (.auth .ok) "decode authOk"
  expectDecode authCleartext (.auth .cleartextPassword) "decode cleartext"
  expectDecode (authMd5 (hex "01 02 03 04")) (.auth (.md5Password (hex "01 02 03 04")))
    "decode md5"
  expectDecode (authSasl #["SCRAM-SHA-256", "SCRAM-SHA-256-PLUS"])
    (.auth (.sasl #["SCRAM-SHA-256", "SCRAM-SHA-256-PLUS"])) "decode sasl"
  expectDecode (authSaslContinue "r=abc") (.auth (.saslContinue (ascii "r=abc")))
    "decode saslContinue"
  expectDecode (authSaslFinal "v=abc") (.auth (.saslFinal (ascii "v=abc")))
    "decode saslFinal"
  expectDecode (backendKeyData 1234 (hex "00 00 16 2e"))
    (.backendKeyData 1234 (hex "00 00 16 2e")) "decode backendKeyData"
  -- 3.2 variable-length cancel key (32 bytes)
  let key32 := hex (String.join (List.replicate 16 "ab cd "))
  expectDecode (backendKeyData 7 key32) (.backendKeyData 7 key32) "decode 3.2 key"
  expectDecode (parameterStatus "server_version" "17.5")
    (.parameterStatus "server_version" "17.5") "decode parameterStatus"
  expectDecode (readyForQuery 'I') (.readyForQuery .idle) "decode ready idle"
  expectDecode (readyForQuery 'T') (.readyForQuery .inTransaction) "decode ready tx"
  expectDecode (readyForQuery 'E') (.readyForQuery .failed) "decode ready failed"
  expectDecode parseComplete .parseComplete "decode parseComplete"
  expectDecode bindComplete .bindComplete "decode bindComplete"
  expectDecode closeComplete .closeComplete "decode closeComplete"
  expectDecode noData .noData "decode noData"
  expectDecode portalSuspended .portalSuspended "decode portalSuspended"
  expectDecode emptyQueryResponse .emptyQueryResponse "decode emptyQuery"
  expectDecode (commandComplete "INSERT 0 3") (.commandComplete "INSERT 0 3")
    "decode commandComplete"
  expectDecode (dataRow #[some (ascii "42"), none, some ByteArray.empty])
    (.dataRow #[some (ascii "42"), none, some ByteArray.empty]) "decode dataRow"
  expectDecode (rowDescription #[col "a" 23, col "b" 25])
    (.rowDescription #[col "a" 23, col "b" 25]) "decode rowDescription"
  expectDecode (errorResponse "ERROR" "42P01" "boom")
    (.errorResponse { fields := #[(83, "ERROR"), (67, "42P01"), (77, "boom")] })
    "decode errorResponse"
  expectDecode (noticeResponse "NOTICE" "00000" "hi")
    (.noticeResponse { fields := #[(83, "NOTICE"), (67, "00000"), (77, "hi")] })
    "decode notice"
  expectDecode (notification 77 "chan" "hi") (.notificationResponse 77 "chan" "hi")
    "decode notification"
  expectDecode (parameterDescription #[23, 25]) (.parameterDescription #[23, 25])
    "decode parameterDescription"
  expectDecode (copyInResponse 0 #[0, 0]) (.copyInResponse 0 #[0, 0]) "decode copyIn"
  expectDecode (copyOutResponse 1 #[1]) (.copyOutResponse 1 #[1]) "decode copyOut"
  expectDecode (copyBothResponse 0 #[]) (.copyBothResponse 0 #[]) "decode copyBoth"
  expectDecode (copyData (ascii "1\tx\n")) (.copyData (ascii "1\tx\n")) "decode copyData"
  expectDecode copyDone .copyDone "decode copyDone"
  expectDecode (negotiateProtocolVersion 0 #["_pq_.x"])
    (.negotiateProtocolVersion 0 #["_pq_.x"]) "decode negotiate"

  -- ErrorFields accessors
  match Backend.decode { tag := 69, payload :=
    (errorFieldsBody #[('S', "ERROR"), ('C', "23505"), ('M', "dup"), ('n', "users_pkey"),
                       ('P', "12"), ('t', "users")]) } with
  | .error e => throw (IO.userError s!"fields decode: {e}")
  | .ok (.errorResponse f) =>
    expectEq f.sqlState? (some "23505") "sqlState"
    expectEq f.message? (some "dup") "message"
    expectEq f.constraintName? (some "users_pkey") "constraint"
    expectEq f.position? (some 12) "position"
    expectEq f.tableName? (some "users") "table"
    expectEq f.hint? none "absent hint"
  | .ok m => throw (IO.userError s!"fields decode: unexpected {repr m}")

  -- ── fragmentation torture over the full catalog ─────────────────────────
  let stream := authOk ++ backendKeyData 1 (hex "00 00 00 01") ++
    parameterStatus "k" "v" ++ readyForQuery 'I' ++
    rowDescription #[col "a" 23] ++ dataRow #[some (ascii "1")] ++
    commandComplete "SELECT 1" ++ errorResponse "ERROR" "0A000" "x" ++
    notification 9 "c" "" ++ copyInResponse 0 #[0] ++ copyData (ascii "z") ++
    copyDone ++ readyForQuery 'E'
  let whole ← parseAll stream 13 "catalog whole"
  let mut st : DecodeState := {}
  for i in [0:stream.size] do
    st ← IO.ofExcept (st.feed (stream.extract i (i + 1)))
  let (frag, st') := st.take
  expect st'.buffered.isEmpty "torture residual"
  expect (frag.size == 13) s!"torture count {frag.size}"
  for i in [0:13] do
    let a ← IO.ofExcept (Backend.decode whole[i]!)
    let b ← IO.ofExcept (Backend.decode frag[i]!)
    expectEq a b s!"torture msg {i}"

  -- truncation: no strict prefix of a message yields a message
  let golden := rowDescription #[col "a" 23]
  for i in [0:golden.size] do
    let trunc ← IO.ofExcept (({} : DecodeState).feed (golden.extract 0 i))
    expect trunc.messages.isEmpty s!"truncated prefix {i}"

  -- ── corrupt payloads must fail to decode ────────────────────────────────
  expectDecodeError 90 (ascii "X") "ready bad status"
  expectDecodeError 90 (hex "49 00") "ready trailing"
  expectDecodeError 82 (hex "00 00 00 05 01 02") "md5 salt short"
  expectDecodeError 82 (hex "00 00 00 0a" ++ ascii "SCRAM") "sasl unterminated"
  expectDecodeError 68 (hex "00 01 00 00 00 05 61") "dataRow value short"
  expectDecodeError 68 (hex "00 01 ff ff ff fe") "dataRow negative len"
  expectDecodeError 75 (hex "00 00 00 01") "key empty secret"
  expectDecodeError 75 (hex "00 00 00 01" ++ ByteArray.mk (Array.replicate 300 0)) "key oversized"
  expectDecodeError 69 (hex "53" ++ ascii "ERROR") "error fields unterminated"
  expectDecodeError 84 (hex "00 01" ++ ascii "a") "rowDescription truncated"
  expectDecodeError 33 ByteArray.empty "unknown tag"
  expectDecodeError 86 (hex "ff ff ff fe") "functionCall negative len"

  IO.println "all wire assertions passed"
