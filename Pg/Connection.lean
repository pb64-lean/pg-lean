module

public import Std.Async.TCP
public import Std.Async.DNS
public import Std.Async.Timer
public import Std.Async.Select
public import Std.Sync.Mutex
public import Std.Time
public import Pg.Protocol.Machine
public import Pg.Sasl.Scram
public import Tls.Client
public import Pg.Tls.TrustStore
public import Pg.Config
public import Pg.Error
public import Pg.Types.Codec

public section

namespace Pg

open Std.Async
open Pg.Protocol

/-!
The async IO shell over the pure `Machine`: a TCP socket, the machine state
behind a `Std.Mutex`, and a queue of asynchronously received notifications.

Concurrency model (v1): one logical operation at a time. Public operations
hold the state mutex across their whole request/response exchange (the
grpc-lean pattern); LISTEN/NOTIFY traffic received meanwhile is queued and
surfaced via `waitNotification`. A notice callback runs while the lock is
held, so it must not call back into the connection.
-/

structure Notification where
  processId : UInt32
  channel : String
  payload : String
  deriving Repr, BEq, Inhabited

/-- One statement's results (simple query protocol). -/
structure Rows where
  columns : Array ColumnDesc := #[]
  rows : Array (Array (Option ByteArray)) := #[]
  /-- CommandComplete tag, e.g. "SELECT 1"; "EMPTY" for an empty query. -/
  tag : String := ""
  deriving Repr, Inhabited

namespace Rows

/-- Typed cell access: `rs.get (α := Int) row col` decodes via the column's
declared OID and wire format. -/
def get (rs : Rows) (row col : Nat) [PgDecode α] : Except String α := do
  let some r := rs.rows[row]? | throw s!"row {row} out of range"
  let some cd := rs.columns[col]? | throw s!"column {col} out of range"
  let some v := r[col]? | throw s!"column {col} missing in row"
  decodeValue cd.typeOid cd.format v

def columnIndex? (rs : Rows) (name : String) : Option Nat :=
  rs.columns.findIdx? (·.name == name)

def getByName (rs : Rows) (row : Nat) (name : String) [PgDecode α] : Except String α := do
  let some col := rs.columnIndex? name | throw s!"no column named {name}"
  rs.get row col

end Rows

structure ConnState where
  machine : Machine.State
  notifications : Array Notification := #[]

structure Connection where
  socket : TCP.Socket.Client
  /-- TLS state is mutated only while `state` is held (except during the
  single-threaded startup handshake). `none` is a plaintext connection. -/
  tls : Option (IO.Ref Tls.Client.State)
  state : Std.Mutex ConnState
  onNotice : ErrorFields → IO Unit
  host : String
  port : UInt16
  connectTimeoutMs : Nat
  /-- Retained so a fresh TLS cancellation connection cannot silently weaken
  the server-identity policy of the original connection. -/
  sslMode : SslMode := .disable
  sslRootCert : Option System.FilePath := none
  /-- BackendKeyData, held outside the op mutex so `cancel` can read it while
  another task's query holds the lock. -/
  cancelKey : Option Machine.BackendKey

private def sendWire (socket : TCP.Socket.Client) (bytes : ByteArray) : IO Unit := do
  if bytes.size > 0 then
    (socket.send bytes).block

private def sendTlsFatalAlert (socket : TCP.Socket.Client)
    (state : Tls.Client.State) (error : Tls.Client.Error) : IO Unit := do
  let some description := error.fatalAlertDescription?
    | return
  match Tls.Client.sealFatalAlert state description with
  | .error _ => pure ()
  | .ok output =>
    try sendWire socket output.wireBytes catch _ => pure ()

private def recvWire (socket : TCP.Socket.Client) : IO (Option ByteArray) :=
  (socket.recv? 65536).block

private def shutdownSocket (socket : TCP.Socket.Client) : IO Unit := do
  try (socket.shutdown).block catch _ => pure ()

private def tlsFailure (context : String) (e : Tls.Client.Error) : IO.Error :=
  IO.userError s!"TLS {context}: {e}"

/-- Apply the libpq peer-verification policy after Finished, while the socket
is still owned by startup. The TLS engine has already strict-parsed the exact
Certificate-list bytes and verified CertificateVerify proof of possession. -/
private def verifyTlsPeer (cfg : ConnectConfig) (state : Tls.Client.State) :
    IO Unit := do
  unless Tls.TrustStore.verificationRequested cfg.sslMode do
    return
  let some loaded ←
      Tls.TrustStore.loadForVerification cfg.sslMode cfg.sslRootCert
    | throw (IO.userError
        "TLS certificate verification failed: no trust store was loaded")
  let some leaf := state.peerCertificates[0]?
    | throw (IO.userError
        "TLS certificate verification failed: server certificate is missing")
  let presented :=
    state.peerCertificates.extract 1 state.peerCertificates.size
  let now :=
    (← Std.Time.Timestamp.now).toSecondsSinceUnixEpoch.toInt
  let verified ←
    match TLS13.X509.Chain.validate now leaf presented loaded.trustStore with
    | .ok verified => pure verified
    | .error failure =>
      throw (IO.userError (toString (Error.tlsChainVerification failure)))
  if cfg.sslMode == .verifyFull then
    match TLS13.X509.Hostname.verifyHostname cfg.host verified.leaf with
    | .ok () => pure ()
    | .error failure =>
      throw (IO.userError (toString (Error.tlsHostnameVerification failure)))

/-- Protect application bytes when TLS is active. The caller serializes access
to `tls` with the connection mutex. -/
private def sendTransport (socket : TCP.Socket.Client)
    (tls : Option (IO.Ref Tls.Client.State)) (bytes : ByteArray) : IO Unit := do
  if bytes.isEmpty then return
  match tls with
  | none => sendWire socket bytes
  | some ref =>
    let state ← ref.get
    match Tls.Client.sealApplication state bytes with
    | .error e =>
      shutdownSocket socket
      throw (tlsFailure "write failed" e)
    | .ok output =>
      try
        sendWire socket output.wireBytes
        ref.set output.state
      catch e =>
        shutdownSocket socket
        throw e

/-- Feed one raw socket chunk through TLS. `some #[]` means a control-only TLS
record (for example NewSessionTicket); `none` means authenticated close_notify.
Any generated control reply (currently KeyUpdate) is written before returning.
-/
private def decodeTransport (socket : TCP.Socket.Client)
    (tls : Option (IO.Ref Tls.Client.State)) (chunk : ByteArray) :
    IO (Option ByteArray) := do
  match tls with
  | none => pure (some chunk)
  | some ref =>
    let state ← ref.get
    match Tls.Client.feedWithFailure state chunk with
    | .error failure =>
      sendTlsFatalAlert socket failure.state failure.error
      shutdownSocket socket
      throw (tlsFailure "read failed" failure.error)
    | .ok output =>
      try
        sendWire socket output.wireBytes
        ref.set output.state
      catch e =>
        shutdownSocket socket
        throw e
      if output.plaintext.isEmpty && output.state.closed then
        pure none
      else
        pure (some output.plaintext)

private partial def recvTransport (socket : TCP.Socket.Client)
    (tls : Option (IO.Ref Tls.Client.State)) : IO (Option ByteArray) := do
  match ← recvWire socket with
  | none =>
    match tls with
    | none => pure none
    | some ref =>
      if (← ref.get).peerClosed then
        pure none
      else
        throw (IO.userError "TLS connection closed without close_notify")
  | some chunk =>
    match ← decodeTransport socket tls chunk with
    | some plaintext =>
      if plaintext.isEmpty then recvTransport socket tls else pure (some plaintext)
    | none => pure none

private def sendBytes (conn : Connection) (bytes : ByteArray) : IO Unit :=
  sendTransport conn.socket conn.tls bytes

private def recvChunk (conn : Connection) : IO (Option ByteArray) :=
  recvTransport conn.socket conn.tls

private def toSocketAddress (addr : Std.Net.IPAddr) (port : UInt16) : Std.Net.SocketAddress :=
  match addr with
  | .v4 a => .v4 { addr := a, port }
  | .v6 a => .v6 { addr := a, port }

private partial def cancellableSleep (remainingMs : Nat) : IO Unit := do
  if remainingMs == 0 || (← IO.checkCanceled) then
    pure ()
  else
    let chunk := min remainingMs 50
    IO.sleep (UInt32.ofNat chunk)
    cancellableSleep (remainingMs - chunk)

/-- Run `act` with a relative timeout; `none` on timeout. The losing task is
cancelled so fragmented handshakes cannot accumulate sleepers or socket reads. -/
private def timedIO (ms : Nat) (act : IO α) : IO (Option α) := do
  if ms == 0 then
    some <$> act
  else
    let work ← IO.asTask (some <$> act)
    let timer ← IO.asTask (do
      cancellableSleep ms
      pure (none : Option α))
    match ← IO.waitAny [work, timer] with
    | .ok result =>
      if result.isSome then IO.cancel timer else IO.cancel work
      pure result
    | .error e =>
      IO.cancel work
      IO.cancel timer
      throw e

private def deadlineFromNow (ms : Nat) : IO (Option Nat) := do
  if ms == 0 then
    pure none
  else
    pure (some ((← IO.monoNanosNow) + ms * 1000000))

private def timedIOUntil (deadline : Option Nat) (act : IO α) : IO (Option α) := do
  match deadline with
  | none => some <$> act
  | some deadline =>
    let now ← IO.monoNanosNow
    if deadline <= now then
      pure none
    else
      let remainingMs := (deadline - now + 999999) / 1000000
      timedIO remainingMs act

private def recvSslResponse (socket : TCP.Socket.Client) (deadline : Option Nat) :
    IO UInt8 := do
  let some response? ← timedIOUntil deadline ((socket.recv? 1).block)
    | throw (IO.userError "PostgreSQL SSLRequest timed out")
  let some response := response?
    | throw (IO.userError "server closed the connection during SSL negotiation")
  -- `recv? 1` should enforce this itself. Keep the check at the trust boundary:
  -- accepting bytes beyond S/N enables pre-handshake buffer injection.
  unless response.size == 1 do
    throw (IO.userError "server sent an invalid response to PostgreSQL SSLRequest")
  pure (response.get! 0)

private def startTls (socket : TCP.Socket.Client) (cfg : ConnectConfig)
    (deadline : Option Nat) :
    IO (IO.Ref Tls.Client.State) := do
  let mut initial? : Option Tls.Client.Output := none
  while initial?.isNone do
    let entropy ← IO.getRandomBytes 128
    let clientCfg : Tls.Client.Config := {
      serverName := if cfg.host.isEmpty then none else some cfg.host
      clientRandom := entropy.extract 0 32
      legacySessionId := entropy.extract 32 64
      x25519Private := entropy.extract 64 96
      p256Private := some (entropy.extract 96 128) }
    match Tls.Client.start clientCfg with
    | .ok output => initial? := some output
    | .error (.invalidPrivateKey .secp256r1) =>
      -- Uniform 256-bit samples very rarely fall outside the P-256 scalar
      -- range. Rejection sampling preserves uniformity without a bignum shim.
      pure ()
    | .error e => throw (tlsFailure "handshake setup failed" e)
  let initial := initial?.get!
  sendWire socket initial.wireBytes
  let mut state := initial.state
  while !state.connected do
    let some chunk? ← timedIOUntil deadline (recvWire socket)
      | throw (IO.userError s!"TLS handshake with {cfg.host} timed out")
    let some chunk := chunk?
      | throw (IO.userError "server closed the connection during TLS handshake")
    let output ← match Tls.Client.feedWithFailure state chunk with
      | .ok output => pure output
      | .error failure =>
        sendTlsFatalAlert socket failure.state failure.error
        throw (tlsFailure "handshake failed" failure.error)
    state := output.state
    -- Application bytes before the server Finished are forbidden by the TLS
    -- engine. Once it reports connected, PostgreSQL still cannot have replied:
    -- its StartupMessage has not been sent yet.
    unless output.plaintext.isEmpty do
      throw (IO.userError "TLS server sent application data before PostgreSQL startup")
    sendWire socket output.wireBytes
  verifyTlsPeer cfg state
  IO.mkRef state

private inductive ConnectPolicy where
  | plaintext
  | negotiateTls (required : Bool)

private def negotiateTransport (socket : TCP.Socket.Client) (cfg : ConnectConfig)
    (policy : ConnectPolicy) (deadline : Option Nat) :
    IO (Option (IO.Ref Tls.Client.State)) := do
  match policy with
  | .plaintext => pure none
  | .negotiateTls required =>
    sendWire socket encodeSSLRequest
    match ← recvSslResponse socket deadline with
    | 83 => some <$> startTls socket cfg deadline  -- 'S'
    | 78 =>                            -- 'N'
      if required then
        throw (IO.userError "server does not support TLS, but sslmode requires it")
      else
        pure none
    | _ =>
      -- In particular, never surface an ErrorResponse smuggled in place of
      -- the one-byte reply (CVE-2024-10977).
      throw (IO.userError "server sent an invalid response to PostgreSQL SSLRequest")

private def connectSocket (host : String) (port : UInt16) : IO TCP.Socket.Client := do
  let addrs ← (DNS.getAddrInfo host (toString port.toNat)).block
  if addrs.isEmpty then
    throw (IO.userError s!"could not resolve {host}")
  let mut lastError : Option IO.Error := none
  for addr in addrs do
    let socket ← TCP.Socket.Client.mk
    try
      (socket.connect (toSocketAddress addr port)).block
      socket.noDelay
      return socket
    catch e =>
      lastError := some e
  throw (lastError.getD (IO.userError s!"could not connect to {host}:{port.toNat}"))

private def connectAttempt (cfg : ConnectConfig) (onNotice : ErrorFields → IO Unit)
    (policy : ConnectPolicy) : IO (Except Machine.PgError Connection) := do
  let deadline ← deadlineFromNow cfg.connectTimeoutMs
  let some socket ← timedIOUntil deadline (connectSocket cfg.host cfg.port)
    | throw (IO.userError s!"connecting to {cfg.host}:{cfg.port.toNat} timed out")
  try
    let tls ← negotiateTransport socket cfg policy deadline
    if cfg.channelBinding == .require && tls.isNone then
      shutdownSocket socket
      return .error (.channelBinding .tlsRequired)
    let tlsServerEndPoint ← match tls with
      | none => pure none
      | some ref =>
        let state ← ref.get
        let some leaf := state.peerCertificates[0]?
          | throw (IO.userError
              "TLS channel binding failed: server certificate is missing")
        pure (some (TLS13.X509.ChannelBinding.tlsServerEndPoint leaf))
    let nonce ← Sasl.Scram.genNonce
    let (m0, startBytes) := Machine.start {
      user := cfg.user
      database := cfg.database
      password := cfg.password
      parameters := cfg.parameters
      requestedVersion := cfg.requestedVersion
      scramNonce := nonce
      channelBinding := cfg.channelBinding
      tlsServerEndPoint }
    sendTransport socket tls startBytes
    let mut m := m0
    let mut notifications : Array Notification := #[]
    let mut ready := false
    while !ready do
      let some chunk? ← timedIOUntil deadline (recvTransport socket tls)
        | throw (IO.userError s!"startup handshake with {cfg.host} timed out")
      match chunk? with
      | none => throw (IO.userError (toString Error.disconnected))
      | some chunk =>
        match Machine.feed m chunk with
        | .error e =>
          shutdownSocket socket
          return .error e
        | .ok (m', events, out) =>
          m := m'
          sendTransport socket tls out
          for ev in events do
            match ev with
            | .ready _ => ready := true
            | .notice fields => onNotice fields
            | .notification pid channel payload =>
              notifications := notifications.push ⟨pid, channel, payload⟩
            | _ => pure ()
    let state ← Std.Mutex.new { machine := m, notifications }
    pure (.ok {
      socket, tls, state, onNotice, host := cfg.host, port := cfg.port
      connectTimeoutMs := cfg.connectTimeoutMs
      sslMode := cfg.sslMode
      sslRootCert := cfg.sslRootCert
      cancelKey := m.cancelKey? })
  catch e =>
    shutdownSocket socket
    throw e

private def indicatesTlsRequired (fields : ErrorFields) : Bool :=
  fields.sqlState? == some "28000" &&
    (fields.message?.map (·.endsWith "no encryption")).getD false

private def indicatesTlsRejected (fields : ErrorFields) : Bool :=
  fields.sqlState? == some "28000" &&
    (fields.message?.map (·.endsWith "SSL encryption")).getD false

private def finishConnectAttempt (result : Except Machine.PgError Connection) :
    IO Connection :=
  match result with
  | .ok conn => pure conn
  | .error (.channelBinding failure) =>
    throw (IO.userError (toString (Error.channelBinding failure)))
  | .error e => throw (IO.userError (toString (Error.fatal e)))

/-- Connect and authenticate. `require` encrypts and verifies CertificateVerify
proof of possession but deliberately does not validate certificate identity.
`verify-ca` additionally validates a path to the configured trust store;
`verify-full` also verifies the connection hostname. Fatal problems throw
`IO.Error`; `onNotice` receives server notices for the connection lifetime. -/
def connect (cfg : ConnectConfig) (onNotice : ErrorFields → IO Unit := fun _ => pure ()) :
    IO Connection := do
  match cfg.sslMode with
  | .disable =>
    finishConnectAttempt (← connectAttempt cfg onNotice .plaintext)
  | .require =>
    finishConnectAttempt (← connectAttempt cfg onNotice (.negotiateTls true))
  | .prefer =>
    match ← connectAttempt cfg onNotice (.negotiateTls false) with
    | .ok conn => pure conn
    | .error (.serverFatal fields) =>
      if indicatesTlsRejected fields then
        finishConnectAttempt (← connectAttempt cfg onNotice .plaintext)
      else
        finishConnectAttempt (.error (.serverFatal fields))
    | .error e => finishConnectAttempt (.error e)
  | .allow =>
    match ← connectAttempt cfg onNotice .plaintext with
    | .ok conn => pure conn
    | .error (.serverFatal fields) =>
      if indicatesTlsRequired fields then
        finishConnectAttempt (← connectAttempt cfg onNotice (.negotiateTls true))
      else
        finishConnectAttempt (.error (.serverFatal fields))
    | .error e => finishConnectAttempt (.error e)
  | .verifyCa =>
    finishConnectAttempt (← connectAttempt cfg onNotice (.negotiateTls true))
  | .verifyFull =>
    finishConnectAttempt (← connectAttempt cfg onNotice (.negotiateTls true))

/-- Connect from a `postgres://` URL. -/
def connectUri (uri : String) (onNotice : ErrorFields → IO Unit := fun _ => pure ()) :
    IO Connection := do
  match ConnectConfig.parseUri uri with
  | .ok cfg => connect cfg onNotice
  | .error e => throw (IO.userError e)

/-- A prepared statement's wire metadata (from Parse + Describe). -/
structure Statement where
  name : String
  paramTypes : Array UInt32 := #[]
  columns : Array ColumnDesc := #[]
  deriving Repr, Inhabited

namespace Connection

/-- Drive the socket until `expectedReady` ReadyForQuery events have arrived,
returning the op-relevant events in wire order (notices go to the callback,
notifications to the queue, ParameterStatus is absorbed by the machine). -/
private partial def driveCollect (conn : Connection) (expectedReady : Nat) :
    Std.AtomicT ConnState IO (Except Error (Array Machine.Event)) := do
  let mut kept : Array Machine.Event := #[]
  let mut seenReady := 0
  let mut outcome : Option (Except Error (Array Machine.Event)) := none
  while outcome.isNone do
    match ← recvChunk conn with
    | none => outcome := some (.error .disconnected)
    | some chunk =>
      let st ← get
      match Machine.feed st.machine chunk with
      | .error e => outcome := some (.error (.fatal e))
      | .ok (m, events, out) =>
        set { st with machine := m }
        sendBytes conn out
        for ev in events do
          match ev with
          | .notice fields => conn.onNotice fields
          | .notification pid channel payload =>
            let n : Notification := ⟨pid, channel, payload⟩
            modify fun s => { s with notifications := s.notifications.push n }
          | .parameterStatus .. => pure ()
          | .ready tx =>
            kept := kept.push (.ready tx)
            seenReady := seenReady + 1
            if seenReady ≥ expectedReady then
              outcome := some (.ok kept)
          | ev => kept := kept.push ev
  pure (outcome.getD (.error .disconnected))

/-- Drive until an event satisfying `isStop` arrives (kept in the returned
array). Async traffic is absorbed as in `driveCollect`. -/
private partial def driveUntilEvent (conn : Connection) (isStop : Machine.Event → Bool) :
    Std.AtomicT ConnState IO (Except Error (Array Machine.Event)) := do
  let mut kept : Array Machine.Event := #[]
  let mut outcome : Option (Except Error (Array Machine.Event)) := none
  while outcome.isNone do
    match ← recvChunk conn with
    | none => outcome := some (.error .disconnected)
    | some chunk =>
      let st ← get
      match Machine.feed st.machine chunk with
      | .error e => outcome := some (.error (.fatal e))
      | .ok (m, events, out) =>
        set { st with machine := m }
        sendBytes conn out
        for ev in events do
          match ev with
          | .notice fields => conn.onNotice fields
          | .notification pid channel payload =>
            let n : Notification := ⟨pid, channel, payload⟩
            modify fun s => { s with notifications := s.notifications.push n }
          | .parameterStatus .. => pure ()
          | ev =>
            kept := kept.push ev
            if isStop ev && outcome.isNone then
              outcome := some (.ok kept)
  pure (outcome.getD (.error .disconnected))

/-- Submit requests and drive to the final ReadyForQuery, returning raw events
— the general pipelining entry point. `reqs` must contain at least one `sync`
or `simpleQuery` (something that produces ReadyForQuery), else the drive could
never terminate. Server errors appear as `errorResponse` events (with the
usual skip-until-Sync semantics), not as `.error`. -/
partial def run (conn : Connection) (reqs : Array Machine.Request) :
    IO (Except Error (Array Machine.Event)) := do
  let expectedReady := reqs.foldl (fun n r =>
    match r with
    | .sync | .simpleQuery _ => n + 1
    | _ => n) 0
  if expectedReady == 0 then
    return .error (.rejected (.rejectedInvalid "run needs a sync or simpleQuery"))
  conn.state.atomically do
    let st ← get
    match Machine.submitAll st.machine reqs with
    | .error e => pure (.error (.rejected e))
    | .ok (m, bytes) =>
      set { st with machine := m }
      sendBytes conn bytes
      driveCollect conn expectedReady

/-- Interpret a simple-query event stream: one `Rows` per statement. -/
private def foldSimple (events : Array Machine.Event) :
    Except Error (Array Rows) := Id.run do
  let mut results : Array Rows := #[]
  let mut current : Rows := {}
  let mut firstError : Option ErrorFields := none
  for ev in events do
    match ev with
    | .rowDescription columns => current := { columns, rows := #[], tag := "" }
    | .dataRow row => current := { current with rows := current.rows.push row }
    | .commandComplete tag =>
      results := results.push { current with tag }
      current := {}
    | .emptyQuery =>
      results := results.push { tag := "EMPTY" }
      current := {}
    | .errorResponse fields =>
      if firstError.isNone then firstError := some fields
    | _ => pure ()
  match firstError with
  | some fields => return .error (.server fields)
  | none => return .ok results

/-- Run one simple-query exchange (`Q`): possibly multiple statements, one
`Rows` per completed statement. A statement error yields `.error (.server _)`
with the connection still usable; fatal errors poison the connection. -/
def query (conn : Connection) (sql : String) : IO (Except Error (Array Rows)) := do
  pure ((← conn.run #[.simpleQuery sql]).bind foldSimple)

/-- `query` for statements where only the command tags matter. -/
def exec (conn : Connection) (sql : String) : IO (Except Error (Array String)) := do
  pure ((← conn.query sql).map (·.map (·.tag)))

private def foldPrepare (name : String) (events : Array Machine.Event) :
    Except Error Statement := Id.run do
  let mut stmt : Statement := { name }
  for ev in events do
    match ev with
    | .parameterDescription oids => stmt := { stmt with paramTypes := oids }
    | .rowDescription columns => stmt := { stmt with columns }
    | .errorResponse fields => return .error (.server fields)
    | _ => pure ()
  return .ok stmt

private def foldExecute (events : Array Machine.Event) : Except Error Rows := Id.run do
  let mut result : Rows := {}
  for ev in events do
    match ev with
    | .rowDescription columns => result := { result with columns }
    | .dataRow row => result := { result with rows := result.rows.push row }
    | .commandComplete tag => result := { result with tag }
    | .emptyQuery => result := { result with tag := "EMPTY" }
    | .errorResponse fields => return .error (.server fields)
    | _ => pure ()
  return .ok result

/-- Parse + Describe + Sync: create a named (or unnamed, `""`) prepared
statement and learn its parameter types and result columns. -/
def prepare (conn : Connection) (name sql : String) (paramTypeOids : Array UInt32 := #[]) :
    IO (Except Error Statement) := do
  pure ((← conn.run #[.parse name sql paramTypeOids, .describeStatement name, .sync]).bind
    (foldPrepare name))

/-- Bind + Describe + Execute + Sync on a prepared statement, draining all
rows. `params` are wire values (text format by default); `none` = NULL. -/
def execute (conn : Connection) (statement : String)
    (params : Array (Option ByteArray) := #[])
    (paramFormats : Array UInt16 := #[])
    (resultFormats : Array UInt16 := #[]) : IO (Except Error Rows) := do
  pure ((← conn.run #[
    .bind "" statement paramFormats params resultFormats,
    .describePortal "",
    .execute "" 0,
    .sync]).bind foldExecute)

/-- Deliver a queued notification, else wait up to `timeoutMs` for one to
arrive on the wire. `none` on timeout. Statement errors cannot occur here;
anything the server sends besides async traffic poisons the connection. -/
partial def waitNotification (conn : Connection) (timeoutMs : Nat := 1000) :
    IO (Except Error (Option Notification)) := do
  conn.state.atomically do
    let st ← get
    if st.notifications.size > 0 then
      let n := st.notifications[0]!
      set { st with notifications := st.notifications.extract 1 st.notifications.size }
      pure (.ok (some n))
    else
      let sleep ← (Sleep.mk (Std.Time.Millisecond.Offset.ofNat timeoutMs)).block
      let mut outcome : Option (Except Error (Option Notification)) := none
      while outcome.isNone do
        let raced ← (Selectable.one #[
          .case (conn.socket.recvSelector 65536) (fun chunk? => pure (some chunk?)),
          .case sleep.selector (fun _ => pure none)]).block
        match raced with
        | none => outcome := some (.ok none)  -- timeout
        | some none => outcome := some (.error .disconnected)
        | some (some wireChunk) =>
          match ← decodeTransport conn.socket conn.tls wireChunk with
          | none => outcome := some (.error .disconnected)
          | some chunk =>
            -- A post-handshake TLS control record can produce no PostgreSQL
            -- bytes. Keep racing the same deadline in that case.
            unless chunk.isEmpty do
              let st ← get
              match Machine.feed st.machine chunk with
              | .error e => outcome := some (.error (.fatal e))
              | .ok (m, events, out) =>
                set { st with machine := m }
                sendBytes conn out
                for ev in events do
                  match ev with
                  | .notice fields => conn.onNotice fields
                  | .notification pid channel payload =>
                    let n : Notification := ⟨pid, channel, payload⟩
                    modify fun s => { s with notifications := s.notifications.push n }
                  | _ => pure ()
                let st ← get
                if st.notifications.size > 0 then
                  let n := st.notifications[0]!
                  set { st with notifications := st.notifications.extract 1 st.notifications.size }
                  outcome := some (.ok (some n))
      pure (outcome.getD (.ok none))

private def firstServerError (events : Array Machine.Event) : Option ErrorFields :=
  events.findSome? fun
    | .errorResponse fields => some fields
    | _ => none

private def commandTag (events : Array Machine.Event) : String :=
  (events.findSome? fun
    | .commandComplete tag => some tag
    | _ => none).getD ""

/-- `COPY ... FROM STDIN` via the simple query protocol: `next` supplies data
chunks (`none` = done; an exception aborts the COPY with CopyFail). Returns
the CommandComplete tag (`"COPY <n>"`). -/
partial def copyIn (conn : Connection) (sql : String) (next : IO (Option ByteArray)) :
    IO (Except Error String) := do
  conn.state.atomically do
    let st ← get
    match Machine.submit st.machine (.simpleQuery sql) with
    | .error e => pure (.error (.rejected e))
    | .ok (m, bytes) =>
      set { st with machine := m }
      sendBytes conn bytes
      match ← driveUntilEvent conn
        (fun e => (e matches .copyInStarted _) || (e matches .ready _)) with
      | .error e => pure (.error e)
      | .ok events =>
        if let some fields := firstServerError events then
          return .error (.server fields)
        unless events.any (· matches .copyInStarted _) do
          return .error (.rejected (.rejectedInvalid s!"not a COPY FROM STDIN statement: {sql}"))
        -- direction reversed: pump user data
        let mut failed : Option String := none
        let mut sending := true
        while sending do
          let chunk? ← try
              next
            catch e =>
              failed := some (toString e)
              pure none
          match chunk? with
          | some chunk =>
            let st ← get
            match Machine.submit st.machine (.copyData chunk) with
            | .error e => return .error (.rejected e)
            | .ok (m, bytes) =>
              set { st with machine := m }
              sendBytes conn bytes
          | none => sending := false
        let finish := match failed with
          | some reason => Machine.Request.copyFail reason
          | none => Machine.Request.copyDone
        let st ← get
        match Machine.submit st.machine finish with
        | .error e => pure (.error (.rejected e))
        | .ok (m, bytes) =>
          set { st with machine := m }
          sendBytes conn bytes
          match ← driveUntilEvent conn (· matches .ready _) with
          | .error e => pure (.error e)
          | .ok events =>
            match firstServerError events with
            | some fields => pure (.error (.server fields))
            | none => pure (.ok (commandTag events))

/-- `copyIn` from an in-memory chunk list. -/
def copyInChunks (conn : Connection) (sql : String) (chunks : Array ByteArray) :
    IO (Except Error String) := do
  let idx ← IO.mkRef 0
  conn.copyIn sql do
    let i ← idx.get
    if h : i < chunks.size then
      idx.set (i + 1)
      pure (some chunks[i])
    else
      pure none

/-- `COPY ... TO STDOUT` via the simple query protocol: every data chunk goes
to `sink`; returns the CommandComplete tag. -/
partial def copyOut (conn : Connection) (sql : String) (sink : ByteArray → IO Unit) :
    IO (Except Error String) := do
  conn.state.atomically do
    let st ← get
    match Machine.submit st.machine (.simpleQuery sql) with
    | .error e => pure (.error (.rejected e))
    | .ok (m, bytes) =>
      set { st with machine := m }
      sendBytes conn bytes
      match ← driveUntilEvent conn (· matches .ready _) with
      | .error e => pure (.error e)
      | .ok events =>
        if let some fields := firstServerError events then
          return .error (.server fields)
        for ev in events do
          if let .copyData data := ev then
            sink data
        pure (.ok (commandTag events))

/-- `LISTEN <channel>`; notifications arrive via `waitNotification`. -/
def listen (conn : Connection) (channel : String) : IO (Except Error Unit) := do
  let quoted := "\"" ++ channel.replace "\"" "\"\"" ++ "\""
  pure ((← conn.exec s!"LISTEN {quoted}").map (fun _ => ()))

/-- `pg_notify(channel, payload)` through a parametrized statement (no
escaping pitfalls). -/
def notify (conn : Connection) (channel payload : String) : IO (Except Error Unit) := do
  let r ← conn.run #[
    .parse "" "SELECT pg_notify($1, $2)",
    .bind "" "" #[] #[some channel.toUTF8, some payload.toUTF8] #[],
    .execute "" 0,
    .sync]
  pure (r.bind (fun events =>
    match firstServerError events with
    | some fields => .error (.server fields)
    | none => .ok ()))

/-- Cancel whatever this connection is executing over a fresh socket. If the
original connection negotiated TLS, the cancellation connection requires a
fresh TLS handshake too, so the BackendKeyData bearer secret is never
downgraded to plaintext. Safe to call while another task holds the operation
mutex. Best-effort by design. -/
def cancel (conn : Connection) : IO Unit := do
  match conn.cancelKey with
  | none => pure ()
  | some key =>
    let deadline ← deadlineFromNow conn.connectTimeoutMs
    let some socket ← timedIOUntil deadline (connectSocket conn.host conn.port)
      | throw (IO.userError
          s!"connecting cancellation socket to {conn.host}:{conn.port.toNat} timed out")
    try
      let cancelCfg : ConnectConfig := {
        host := conn.host
        port := conn.port
        connectTimeoutMs := conn.connectTimeoutMs
        sslMode := conn.sslMode
        sslRootCert := conn.sslRootCert }
      let tls ←
        if conn.tls.isSome then
          negotiateTransport socket cancelCfg (.negotiateTls true) deadline
        else
          pure none
      sendTransport socket tls (encodeCancelRequest key.processId key.secret)
      -- The server normally closes immediately after consuming CancelRequest.
      -- Attempt a clean TLS shutdown without turning a dispatched cancellation
      -- into a failure if the peer wins that race.
      if let some ref := tls then
        try
          let output ← match Tls.Client.closeNotify (← ref.get) with
            | .ok output => pure output
            | .error e => throw (tlsFailure "cancellation shutdown failed" e)
          ref.set output.state
          sendWire socket output.wireBytes
        catch _ => pure ()
      shutdownSocket socket
    catch e =>
      shutdownSocket socket
      throw e

/-- The latest backend-reported value of a run-time parameter. -/
def parameter? (conn : Connection) (name : String) : IO (Option String) := do
  conn.state.atomically do
    pure ((← get).machine.parameter? name)

/-- The effective protocol version (post-NegotiateProtocolVersion). -/
def protocolVersion (conn : Connection) : IO Machine.ProtocolVersion := do
  conn.state.atomically do
    pure (← get).machine.protocolVersion

/-- SASL mechanism negotiated while authenticating this connection. `none`
means the server selected a non-SASL authentication method. -/
def negotiatedSaslMechanism? (conn : Connection) : IO (Option String) := do
  conn.state.atomically do
    pure (← get).machine.negotiatedSaslMechanism?

/-- Whether PostgreSQL application traffic on this connection is protected by
TLS. This says nothing about certificate identity validation. -/
def usesTls (conn : Connection) : Bool :=
  conn.tls.isSome

/-- The server-supplied leaf certificate DER when TLS is active. The TLS
handshake has verified proof of possession through CertificateVerify, but the
certificate chain and hostname remain unverified until a verification mode
performs those policy checks. -/
def peerCertificate? (conn : Connection) : IO (Option ByteArray) := do
  match conn.tls with
  | none => pure none
  | some ref => pure (← ref.get).leafCertificate?

/-- Graceful shutdown: Terminate, then close the socket. Safe to call on a
poisoned connection. A TLS connection also emits `close_notify`. -/
def close (conn : Connection) : IO Unit := do
  conn.state.atomically do
    let st ← get
    match Machine.submit st.machine .terminate with
    | .ok (m, bytes) =>
      set { st with machine := m }
      try sendBytes conn bytes catch _ => pure ()
    | .error _ => pure ()
    match conn.tls with
    | none => pure ()
    | some ref =>
      try
        let tlsState ← ref.get
        match Tls.Client.closeNotify tlsState with
        | .error _ => pure ()
        | .ok output =>
          ref.set output.state
          sendWire conn.socket output.wireBytes
      catch _ => pure ()
  shutdownSocket conn.socket

end Connection

end Pg
