import Std.Async.TCP
import Pg.Connection
import Pg.Config
import Test.Support.Hex
import Test.Support.Backend

/-!
The Connection shell against an in-process fake server on a loopback socket:
startup exchange over real TCP, a simple query whose response is deliberately
split mid-message across sends, notification queuing + `waitNotification`
timeout (selector + timer race), URL parsing, and EOF mid-conversation.
-/

open Std.Async
open Pg
open Pg.Protocol
open Pg.TestSupport
open Pg.TestSupport.Be

def expect (cond : Bool) (msg : String) : IO Unit := do
  unless cond do throw (IO.userError msg)

private def runAsync (action : Async α) : IO α := action.block

partial def readAtLeast (client : TCP.Socket.Client) (n : Nat)
    (acc : ByteArray := ByteArray.empty) : IO ByteArray := do
  if acc.size ≥ n then
    return acc
  match ← (client.recv? 8192).block with
  | none => throw (IO.userError "fake server: unexpected EOF")
  | some chunk => readAtLeast client n (acc ++ chunk)

/-- Read one untagged startup message (length includes itself). The client
sends nothing after it until the server answers, so plain reads are safe
here. -/
def readStartup (client : TCP.Socket.Client) : IO ByteArray := do
  let head ← readAtLeast client 4
  let some len := getUInt32? head 0 | throw (IO.userError "fake server: short startup")
  readAtLeast client len.toNat head

/-- Post-startup server side of a connection: tagged frontend messages arrive
batched in single TCP chunks (the client writes whole pipelines at once), so
reads go through a buffering DecodeState. -/
structure ServerConn where
  client : TCP.Socket.Client
  pending : IO.Ref (Array RawMessage)
  decode : IO.Ref DecodeState

def ServerConn.mk' (client : TCP.Socket.Client) : IO ServerConn := do
  pure { client, pending := ← IO.mkRef #[], decode := ← IO.mkRef {} }

partial def readMsg (sc : ServerConn) : IO RawMessage := do
  let q ← sc.pending.get
  if q.size > 0 then
    sc.pending.set (q.extract 1 q.size)
    return q[0]!
  match ← (sc.client.recv? 8192).block with
  | none => throw (IO.userError "fake server: unexpected EOF")
  | some chunk =>
    let st ← sc.decode.get
    match st.feed chunk with
    | .error e => throw (IO.userError s!"fake server: {e}")
    | .ok fed =>
      let (msgs, rest) := fed.take
      sc.decode.set rest
      sc.pending.set msgs
      readMsg sc

def readTagged (sc : ServerConn) : IO UInt8 := do
  pure (← readMsg sc).tag

def send (client : TCP.Socket.Client) (bytes : ByteArray) : IO Unit :=
  (client.send bytes).block

/-- Read and validate the complete, untagged SSLRequest. The client must wait
for the one-byte response before sending anything else. -/
def readSslRequest (client : TCP.Socket.Client) : IO Unit := do
  let request ← readAtLeast client encodeSSLRequest.size
  expect (request == encodeSSLRequest) "SSL server: exact SSLRequest"

/-- `sslmode=prefer`: reject TLS, then complete a normal plaintext startup. -/
def serveSslPreferN (server : TCP.Socket.Server) : IO Unit := do
  let client ← server.accept.block
  readSslRequest client
  send client (ByteArray.empty.push 78)  -- 'N'
  let startup ← readStartup client
  expect (getUInt32? startup 4 == some protocolVersion)
    "SSL prefer server: plaintext startup after N"
  let sc ← ServerConn.mk' client
  send client (authOk ++ readyForQuery 'I')
  let tag ← readTagged sc
  expect (tag == 88) "SSL prefer server: expected Terminate"
  (client.shutdown).block

/-- Reply to SSLRequest and then require the client to close without sending a
StartupMessage. Used for both required-TLS rejection and malformed replies. -/
def serveSslNoStartup (server : TCP.Socket.Server) (response : UInt8) : IO Unit := do
  let client ← server.accept.block
  readSslRequest client
  send client (ByteArray.empty.push response)
  match ← (client.recv? 8192).block with
  | none => pure ()
  | some bytes =>
    throw (IO.userError s!"SSL server: client sent {bytes.size} byte(s) after rejected negotiation")

/-- Close immediately after receiving SSLRequest, without sending S or N. -/
def serveSslNegotiationEof (server : TCP.Socket.Server) : IO Unit := do
  let client ← server.accept.block
  readSslRequest client
  (client.shutdown).block

/-- A `channel_binding=require` plaintext attempt must close before sending
even a StartupMessage. -/
def servePlainNoStartup (server : TCP.Socket.Server) : IO Unit := do
  let client ← server.accept.block
  match ← (client.recv? 8192).block with
  | none => pure ()
  | some bytes =>
    throw (IO.userError
      s!"plaintext server: client sent {bytes.size} byte(s) despite channel_binding=require")

/-- Happy-path server: trust auth, one query answered with the response split
mid-message, a notification snuck in, then EOF after Terminate. -/
def serveHappy (server : TCP.Socket.Server) : IO Unit := do
  let client ← server.accept.block
  let startup ← readStartup client
  expect (getUInt32? startup 4 == some protocolVersion) "server: startup version"
  let sc ← ServerConn.mk' client
  send client (authOk ++ backendKeyData 7 (hex "00 00 00 2a") ++
    parameterStatus "server_version" "17.5" ++ readyForQuery 'I')
  let tag ← readTagged sc
  expect (tag == 81) "server: expected Query"  -- 'Q'
  let response := rowDescription #[col "?column?" 23] ++ row #["1"] ++
    notification 9 "jobs" "hello" ++ commandComplete "SELECT 1" ++ readyForQuery 'I'
  -- split mid-message to exercise reassembly over real TCP
  send client (response.extract 0 17)
  send client (response.extract 17 response.size)
  let tag ← readTagged sc
  expect (tag == 88) "server: expected Terminate"  -- 'X'
  (client.shutdown).block

/-- Extended-protocol server: prepare, execute with a row, a failing execute
(error + recovery), then a simple query to prove the connection survived. -/
def serveExtended (server : TCP.Socket.Server) : IO Unit := do
  let client ← server.accept.block
  let _ ← readStartup client
  let sc ← ServerConn.mk' client
  send client (authOk ++ readyForQuery 'I')
  -- prepare: Parse + Describe(S) + Sync
  for _ in [0:3] do
    let _ ← readTagged sc
  send client (parseComplete ++ parameterDescription #[23] ++
    rowDescription #[col "sum" 23] ++ readyForQuery 'I')
  -- execute: Bind + Describe(P) + Execute + Sync
  for _ in [0:4] do
    let _ ← readTagged sc
  send client (bindComplete ++ rowDescription #[col "sum" 23] ++ row #["8"] ++
    commandComplete "SELECT 1" ++ readyForQuery 'I')
  -- failing execute: Bind + Describe(P) + Execute + Sync → error, recovery
  for _ in [0:4] do
    let _ ← readTagged sc
  send client (errorResponse "ERROR" "22012" "division by zero" ++ readyForQuery 'I')
  -- recovery proof: simple Query
  let tag ← readTagged sc
  expect (tag == 81) "server: expected recovery Query"
  send client (rowDescription #[col "ok" 25] ++ row #["yes"] ++
    commandComplete "SELECT 1" ++ readyForQuery 'I')
  let tag ← readTagged sc
  expect (tag == 88) "server: expected Terminate"
  (client.shutdown).block

/-- COPY server: one COPY IN (reads data frames until CopyDone), then one
COPY OUT streamed in awkward chunk boundaries. -/
partial def serveCopy (server : TCP.Socket.Server) : IO Unit := do
  let client ← server.accept.block
  let _ ← readStartup client
  let sc ← ServerConn.mk' client
  send client (authOk ++ readyForQuery 'I')
  -- COPY IN
  let tag ← readTagged sc
  expect (tag == 81) "copy server: expected Query"
  send client (copyInResponse 0 #[])
  let mut received := ByteArray.empty
  let mut rows := 0
  let mut copying := true
  while copying do
    let msg ← readMsg sc
    if msg.tag == 100 then  -- 'd'
      received := received ++ msg.payload
      rows := rows + 1
    else if msg.tag == 99 then  -- 'c' CopyDone
      copying := false
    else
      throw (IO.userError s!"copy server: unexpected tag {msg.tag}")
  expect (received == ascii "1\ta\n2\tb\n3\tc\n") "copy server: received data"
  send client (commandComplete s!"COPY {rows}" ++ readyForQuery 'I')
  -- COPY OUT
  let tag ← readTagged sc
  expect (tag == 81) "copy server: expected second Query"
  let out := copyOutResponse 0 #[] ++ copyData (ascii "x\t1\n") ++
    copyData (ascii "y\t2\n") ++ copyDone ++ commandComplete "COPY 2" ++
    readyForQuery 'I'
  send client (out.extract 0 23)
  send client (out.extract 23 out.size)
  let tag ← readTagged sc
  expect (tag == 88) "copy server: expected Terminate"
  (client.shutdown).block

/-- While no request is pending, send an asynchronous notification, then
accept two request batches before either response is written.  The server
answers both in one TCP chunk, in wire order, with payloads derived from the
received SQL so caller attribution can be checked independently of task
scheduling order. -/
def serveConcurrent (server : TCP.Socket.Server) (sendIdle : IO.Promise Unit)
    (requestCount : Nat) : IO Unit := do
  let client ← server.accept.block
  let _ ← readStartup client
  let sc ← ServerConn.mk' client
  send client (authOk ++ readyForQuery 'I')
  -- The client releases this gate only after `connect` has returned and its
  -- background reader is running, so this exercises truly idle routing.
  match sendIdle.result?.get with
  | none => throw (IO.userError "concurrent server: idle-notification gate dropped")
  | some () => send client (notification 11 "idle_jobs" "ready")
  let mut requests : Array RawMessage := #[]
  for _ in [0:requestCount] do
    let request ← readMsg sc
    expect (request.tag == 81) "concurrent server: expected Query message"
    requests := requests.push request
  let queryText (msg : RawMessage) : String :=
    (String.fromUTF8? (msg.payload.extract 0 (msg.payload.size - 1))).getD ""
  let response (sql : String) : ByteArray :=
    rowDescription #[col "value" 25] ++ row #[sql] ++
      commandComplete "SELECT 1" ++ readyForQuery 'I'
  send client (requests.foldl (fun bytes request =>
    bytes ++ response (queryText request)) ByteArray.empty)
  let tag ← readTagged sc
  expect (tag == 88) "concurrent server: expected Terminate"
  (client.shutdown).block

/-- EOF server: dies mid-response. -/
def serveEof (server : TCP.Socket.Server) : IO Unit := do
  let client ← server.accept.block
  let _ ← readStartup client
  let sc ← ServerConn.mk' client
  send client (authOk ++ readyForQuery 'I')
  let _ ← readTagged sc
  let partial' := rowDescription #[col "a" 23]
  send client (partial'.extract 0 6)
  (client.shutdown).block

def mkServer : IO (TCP.Socket.Server × UInt16) := do
  let server ← TCP.Socket.Server.mk
  server.bind (.v4 { addr := Std.Net.IPv4Addr.ofParts 127 0 0 1, port := 0 })
  server.listen 4
  match ← server.getSockName with
  | .v4 sa => pure (server, sa.port)
  | .v6 _ => throw (IO.userError "unexpected v6 loopback")

def expectConnectFailure (cfg : ConnectConfig) (label : String) : IO Unit := do
  let failed ← try
      let conn ← runAsync (connect cfg)
      runAsync conn.close
      pure false
    catch _ =>
      pure true
  expect failed label

def expectConnectFailureContaining (cfg : ConnectConfig) (needle label : String) :
    IO Unit := do
  try
    let conn ← runAsync (connect cfg)
    runAsync conn.close
    throw (IO.userError s!"{label}: connection unexpectedly succeeded")
  catch e =>
    unless (toString e).contains needle do
      throw (IO.userError s!"{label}: expected {needle}, got {e}")

def main : IO Unit := do
  -- Stable, actionable TLS identity failures for callers and the live matrix.
  expect ((toString (Pg.Error.tlsChainVerification
    (.unknownIssuer 7))).contains "unknown issuer")
    "unknown issuer TLS error reason"
  expect ((toString (Pg.Error.tlsChainVerification
    (.expired 7 10 11))).contains "expired")
    "expired TLS error reason"
  expect ((toString (Pg.Error.tlsChainVerification
    (.leafDigitalSignatureMissing 7))).contains
      "leaf certificate cannot sign TLS handshakes")
    "leaf digitalSignature TLS error reason"
  expect ((toString (Pg.Error.tlsHostnameVerification
    .dnsSubjectAltNameMismatch)).contains "hostname")
    "hostname TLS error reason"
  expect ((toString (Pg.Error.channelBinding .tlsRequired)).contains
    "channel_binding=require requires TLS")
    "channel binding TLS-required reason"
  expect ((toString (Pg.Error.channelBinding .plusNotOffered)).contains
    "SCRAM-SHA-256-PLUS")
    "channel binding PLUS-required reason"

  -- URL parsing
  match ConnectConfig.parseUri
    "postgres://alice:s%40crett@db.example.com:5433/orders?application_name=probe&sslmode=disable&sslrootcert=%2Ftls%2Froot%20ca.pem&channel_binding=require" with
  | .error e => throw (IO.userError s!"parseUri: {e}")
  | .ok cfg =>
    expect (cfg.user == "alice") "uri user"
    expect (cfg.password == some "s@crett") "uri password percent-decode"
    expect (cfg.host == "db.example.com") "uri host"
    expect (cfg.port == 5433) "uri port"
    expect (cfg.database == some "orders") "uri db"
    expect (cfg.sslMode == .disable) "uri sslmode disable"
    expect (cfg.sslRootCert.map (·.toString) == some "/tls/root ca.pem")
      "uri sslrootcert percent-decode"
    expect (cfg.channelBinding == .require) "uri channel_binding require"
    expect (cfg.parameters == #[("application_name", "probe")]) "uri params"
  let sslModes : Array (String × SslMode) := #[
    ("disable", .disable),
    ("allow", .allow),
    ("prefer", .prefer),
    ("require", .require),
    ("verify-ca", .verifyCa),
    ("verify-full", .verifyFull)]
  for (name, want) in sslModes do
    match ConnectConfig.parseUri s!"postgres://u@h?sslmode={name}" with
    | .ok cfg => expect (cfg.sslMode == want) s!"sslmode={name}"
    | .error e => throw (IO.userError s!"sslmode={name}: {e}")
  match ConnectConfig.parseUri "postgres://u@h" with
  | .ok cfg => do
    expect (cfg.sslMode == .disable) "sslmode default disable"
    expect cfg.sslRootCert.isNone "sslrootcert default absent"
    expect (cfg.channelBinding == .prefer) "channel_binding default prefer"
  | .error e => throw (IO.userError s!"sslmode default: {e}")
  expect ((ConnectConfig.parseUri "postgres://u@h?sslmode=bogus") matches .error _)
    "unknown sslmode rejected"
  let channelBindingModes : Array (String × ChannelBindingMode) := #[
    ("prefer", .prefer), ("require", .require), ("disable", .disable)]
  for (name, want) in channelBindingModes do
    match ConnectConfig.parseUri s!"postgres://u@h?channel_binding={name}" with
    | .ok cfg =>
      expect (cfg.channelBinding == want) s!"channel_binding={name}"
    | .error e => throw (IO.userError s!"channel_binding={name}: {e}")
  expect ((ConnectConfig.parseUri
    "postgres://u@h?channel_binding=bogus") matches .error _)
    "unknown channel_binding rejected"
  expect ((ConnectConfig.parseUri "http://u@h") matches .error _) "wrong scheme"
  expect ((ConnectConfig.parseUri "postgres://h") matches .error _) "missing user"
  -- Percent-encoding is a proved inverse of percent-decoding
  -- (`ConnectConfig.percentDecode_percentEncode`), non-ASCII included: the live
  -- matrix connects as `pg-lean-läuft`.
  for probe in #["pg-lean-läuft", "s@cr:et/pa?ss&wd=1%", "", "ok"] do
    expect (ConnectConfig.percentDecode (ConnectConfig.percentEncode probe) == probe)
      s!"percent-encoding roundtrip for {probe}"
  match ConnectConfig.parseUri
      (ConnectConfig.renderUri { user := "pg-lean-läuft", password := some "s@cr:et/1"
                                 host := "db.example.com", port := 5433
                                 database := some "orders/π" }) with
  | .error e => throw (IO.userError s!"render/parse roundtrip: {e}")
  | .ok cfg =>
    expect (cfg.user == "pg-lean-läuft") "rendered URI user"
    expect (cfg.password == some "s@cr:et/1") "rendered URI password"
    expect (cfg.host == "db.example.com") "rendered URI host"
    expect (cfg.port == 5433) "rendered URI port"
    expect (cfg.database == some "orders/π") "rendered URI database"

  -- `require` without TLS fails before PostgreSQL startup, with a stable
  -- channel-binding-specific error.
  let (plainRequireServer, plainRequirePort) ← mkServer
  let plainRequireTask ← IO.asTask (servePlainNoStartup plainRequireServer)
  expectConnectFailureContaining {
      host := "127.0.0.1"
      port := plainRequirePort
      user := "u"
      sslMode := .disable
      channelBinding := .require
    } "channel_binding=require requires TLS"
    "channel_binding=require plaintext"
  match plainRequireTask.get with
  | .ok () => pure ()
  | .error e => throw e

  -- PostgreSQL's unframed SSLRequest negotiation.
  let (sslPreferServer, sslPreferPort) ← mkServer
  let sslPreferTask ← IO.asTask (serveSslPreferN sslPreferServer)
  let sslPreferConn ← runAsync (connect {
    host := "127.0.0.1", port := sslPreferPort, user := "u", sslMode := .prefer })
  runAsync sslPreferConn.close
  match sslPreferTask.get with
  | .ok () => pure ()
  | .error e => throw e

  let (sslRequireServer, sslRequirePort) ← mkServer
  let sslRequireTask ← IO.asTask (serveSslNoStartup sslRequireServer 78)  -- 'N'
  expectConnectFailure {
    host := "127.0.0.1", port := sslRequirePort, user := "u", sslMode := .require }
    "sslmode=require rejects N"
  match sslRequireTask.get with
  | .ok () => pure ()
  | .error e => throw e

  let (sslInvalidServer, sslInvalidPort) ← mkServer
  let sslInvalidTask ← IO.asTask (serveSslNoStartup sslInvalidServer 69)  -- 'E'
  expectConnectFailure {
    host := "127.0.0.1", port := sslInvalidPort, user := "u", sslMode := .require }
    "invalid SSL response rejected"
  match sslInvalidTask.get with
  | .ok () => pure ()
  | .error e => throw e

  let (sslEofServer, sslEofPort) ← mkServer
  let sslEofTask ← IO.asTask (serveSslNegotiationEof sslEofServer)
  expectConnectFailure {
    host := "127.0.0.1", port := sslEofPort, user := "u", sslMode := .require }
    "SSL negotiation EOF rejected"
  match sslEofTask.get with
  | .ok () => pure ()
  | .error e => throw e

  -- happy path over loopback
  let (server, port) ← mkServer
  let serverTask ← IO.asTask (serveHappy server)
  let inactiveRoot : System.FilePath := "/must/not/be/read/root.crt"
  let conn ← runAsync (connect {
    host := "127.0.0.1", port, user := "u", database := some "d"
    sslRootCert := some inactiveRoot
  })
  expect (conn.sslMode == .disable && conn.sslRootCert == some inactiveRoot)
    "connection did not retain TLS policy for cancellation"
  expect ((← runAsync conn.negotiatedSaslMechanism?).isNone)
    "trust-auth connection unexpectedly retained a SASL mechanism"

  -- A TLS connection must also negotiate TLS on its fresh cancellation
  -- socket. If that server replies N, cancel fails closed after the exact
  -- SSLRequest instead of exposing BackendKeyData in a raw CancelRequest.
  let (cancelServer, cancelPort) ← mkServer
  let cancelTask ← IO.asTask (serveSslNoStartup cancelServer 78)  -- 'N'
  let tlsMarker ← IO.mkRef ({
    phase := .connected
    x25519Private := ByteArray.empty
    legacySessionId := ByteArray.empty
  } : Tls.Client.State)
  let tlsCancelConn := {
    conn with
    tls := some tlsMarker
    port := cancelPort
    connectTimeoutMs := 1000
  }
  let cancelRejected ← try
      runAsync tlsCancelConn.cancel
      pure false
    catch _ =>
      pure true
  expect cancelRejected "TLS cancellation rejects an N response"
  match cancelTask.get with
  | .ok () => pure ()
  | .error e => throw e

  expect ((← runAsync (conn.parameter? "server_version")) == some "17.5") "param tracked"
  match ← runAsync (conn.query "SELECT 1") with
  | .error e => throw (IO.userError s!"query: {toString e}")
  | .ok results =>
    expect (results.size == 1) "one statement result"
    expect (results[0]!.columns.map (·.name) == #["?column?"]) "column name"
    expect (results[0]!.rows.size == 1) "one row"
    expect (results[0]!.rows[0]! == #[some (ascii "1")]) "row value"
    expect (results[0]!.tag == "SELECT 1") "tag"
  -- the notification that arrived mid-query is queued
  match ← runAsync (conn.waitNotification 50) with
  | .ok (some n) =>
    expect (n.channel == "jobs" && n.payload == "hello" && n.processId == 9) "notification"
  | other => throw (IO.userError s!"waitNotification: {repr (match other with | .ok n => n | _ => none)}")
  -- nothing further: timeout path (selector vs timer race)
  match ← runAsync (conn.waitNotification 100) with
  | .ok none => pure ()
  | .ok (some n) => throw (IO.userError s!"unexpected notification {repr n}")
  | .error e => throw (IO.userError s!"waitNotification timeout: {toString e}")
  runAsync conn.close
  match serverTask.get with
  | .ok () => pure ()
  | .error e => throw e

  -- extended protocol against the fake server
  let (server3, port3) ← mkServer
  let serverTask3 ← IO.asTask (serveExtended server3)
  let conn3 ← runAsync (connect { host := "127.0.0.1", port := port3, user := "u" })
  match ← runAsync (conn3.prepare "st" "SELECT $1::int4 + $2::int4 AS sum") with
  | .error e => throw (IO.userError s!"prepare: {toString e}")
  | .ok stmt =>
    expect (stmt.paramTypes == #[23]) "statement param types"
    expect (stmt.columns.map (·.name) == #["sum"]) "statement columns"
  match ← runAsync (conn3.execute "st" #[some (ascii "3"), some (ascii "5")]) with
  | .error e => throw (IO.userError s!"execute: {toString e}")
  | .ok rows =>
    expect (rows.columns.map (·.name) == #["sum"]) "execute columns"
    expect (rows.rows == #[#[some (ascii "8")]]) "execute row"
    expect (rows.tag == "SELECT 1") "execute tag"
  match ← runAsync (conn3.execute "st" #[some (ascii "1"), some (ascii "0")]) with
  | .error (.server fields) =>
    expect (fields.sqlState? == some "22012") "execute server error sqlstate"
  | other => throw (IO.userError s!"expected server error, got ok/other ({other matches .ok _})")
  -- the connection survived the error
  match ← runAsync (conn3.query "SELECT 'yes' AS ok") with
  | .error e => throw (IO.userError s!"recovery query: {toString e}")
  | .ok results => expect (results[0]!.rows == #[#[some (ascii "yes")]]) "recovery row"
  runAsync conn3.close
  match serverTask3.get with
  | .ok () => pure ()
  | .error e => throw e

  -- COPY IN / COPY OUT through the shell
  let (server4, port4) ← mkServer
  let serverTask4 ← IO.asTask (serveCopy server4)
  let conn4 ← runAsync (connect { host := "127.0.0.1", port := port4, user := "u" })
  match ← runAsync (conn4.copyInChunks "COPY t FROM STDIN"
      #[ascii "1\ta\n", ascii "2\tb\n", ascii "3\tc\n"]) with
  | .error e => throw (IO.userError s!"copyIn: {toString e}")
  | .ok tag => expect (tag == "COPY 3") s!"copyIn tag {tag}"
  let collected ← IO.mkRef ByteArray.empty
  match ← runAsync (conn4.copyOut "COPY t TO STDOUT" (fun b => collected.modify (· ++ b))) with
  | .error e => throw (IO.userError s!"copyOut: {toString e}")
  | .ok tag => expect (tag == "COPY 2") s!"copyOut tag {tag}"
  expect ((← collected.get) == ascii "x\t1\ny\t2\n") "copyOut data"
  runAsync conn4.close
  match serverTask4.get with
  | .ok () => pure ()
  | .error e => throw e

  -- Concurrent batches share one reader/writer but retain distinct owners.
  let (concurrentServer, concurrentPort) ← mkServer
  let sendIdle ← IO.Promise.new
  let burstSize := 32
  let concurrentServerTask ← IO.asTask
    (serveConcurrent concurrentServer sendIdle burstSize)
  let concurrentConn ← runAsync (connect {
    host := "127.0.0.1", port := concurrentPort, user := "u" })
  discard <| sendIdle.resolve ()
  match ← runAsync (concurrentConn.waitNotification 1000) with
  | .ok (some n) =>
    expect (n.channel == "idle_jobs" && n.payload == "ready" && n.processId == 11)
      "idle notification attribution"
  | other =>
    throw (IO.userError s!"idle waitNotification: {repr (match other with | .ok n => n | _ => none)}")
  -- Invalid generic batches fail before writing anything or perturbing the
  -- coordinator's protocol state.
  let expectRejected (result : Except Pg.Error (Array Machine.Event)) (label : String) :=
    expect (result matches .error (.rejected _)) label
  expectRejected (← runAsync (concurrentConn.run #[])) "empty run rejected"
  expectRejected (← runAsync (concurrentConn.run #[.parse "" "SELECT 1"]))
    "unbounded run rejected"
  expectRejected (← runAsync (concurrentConn.run #[.simpleQuery "SELECT 1", .simpleQuery "SELECT 2"]))
    "multiple response boundaries rejected"
  expectRejected (← runAsync (concurrentConn.run #[.flush, .sync]))
    "control request rejected"
  -- Release a synchronized burst of callers.  The server withholds all
  -- replies until every Query is on the wire, which makes any divergence
  -- between coordinator/owner order and writer-queue order swap results.
  let ready : Std.CloseableChannel Unit ← Std.CloseableChannel.new
  let startBurst ← IO.Promise.new
  let mut queryTasks := #[]
  for i in [0:burstSize] do
    let task ← Async.toIO do
      discard <| ready.trySend ()
      await startBurst
      concurrentConn.query s!"burst-{i}"
    queryTasks := queryTasks.push task
  for _ in [0:burstSize] do
    runAsync do
      match ← await (← ready.recv) with
      | some () => pure ()
      | none => throw (IO.userError "concurrent barrier closed early")
  discard <| startBurst.resolve ()
  let value (result : Except Pg.Error (Array Pg.Rows)) : Option ByteArray :=
    result.toOption.bind fun results =>
      results[0]?.bind fun rows =>
        rows.rows[0]?.bind fun cells => cells[0]?.bind id
  -- Await in reverse creation order: no caller may need to drive the shared
  -- socket, and every response must still reach the owner of its SQL text.
  for offset in [0:burstSize] do
    let i := burstSize - 1 - offset
    let result ← runAsync (Async.ofAsyncTask queryTasks[i]!)
    expect (value result == some (ascii s!"burst-{i}"))
      s!"concurrent burst attribution {i}"
  let closeOne ← Async.toIO concurrentConn.close
  let closeTwo ← Async.toIO concurrentConn.close
  runAsync (Async.ofAsyncTask closeTwo)
  runAsync (Async.ofAsyncTask closeOne)
  expect ((← runAsync (concurrentConn.query "SELECT 'after close'")) matches .error .closed)
    "work after close rejected"
  match concurrentServerTask.get with
  | .ok () => pure ()
  | .error e => throw e

  -- EOF mid-response poisons the query with .disconnected
  let (server2, port2) ← mkServer
  let serverTask2 ← IO.asTask (serveEof server2)
  let conn2 ← runAsync (connect { host := "127.0.0.1", port := port2, user := "u" })
  match ← runAsync (conn2.query "SELECT 1") with
  | .error .disconnected => pure ()
  | .error e => throw (IO.userError s!"expected disconnected, got {toString e}")
  | .ok _ => throw (IO.userError "expected disconnected, got ok")
  runAsync conn2.close
  match serverTask2.get with
  | .ok () => pure ()
  | .error e => throw e

  IO.println "all connection assertions passed"
