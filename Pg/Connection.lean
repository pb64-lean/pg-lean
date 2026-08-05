module

public import Std.Async.TCP
public import Std.Async.DNS
public import Std.Async.Timer
public import Std.Async.Select
public import Std.Sync.Mutex
public import Std.Sync.Channel
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
The cooperative shell over the pure `Machine`.  One reader owns socket reads,
one writer owns socket writes, and a short coordinator mutex sequences bounded
machine/routing transitions, TLS record advancement, and FIFO insertion. Public
operations may therefore pipeline concurrently without holding a worker or a
mutex while waiting for the peer. Caller tags are erased by
`Machine.tagged_feed_fifo`, so routing is a refinement of the machine's verified
FIFO rather than a second protocol implementation.
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

inductive Life where
  | open
  | closing
  | closed
  deriving BEq, Inhabited

structure PendingCall where
  owner : Machine.OwnerId
  events : Array Machine.Event := #[]
  completion : IO.Promise (Except Error (Array Machine.Event))
  copyStarted : Option (IO.Promise (Except Error Machine.CopyInfo)) := none
  copyData : Option (Std.CloseableChannel ByteArray) := none

structure ConnState where
  machine : Machine.State
  routing : List Machine.TaggedOp := []
  pending : Array PendingCall := #[]
  nextOwner : Machine.OwnerId := 0
  life : Life := .open
  /-- COPY reverses or streams the wire direction.  No later batch is admitted
  until its ReadyForQuery boundary has retired this owner. -/
  exclusiveOwner : Option Machine.OwnerId := none

inductive Outbound where
  /-- Plaintext PostgreSQL is unchanged; TLS records are sealed before they
  enter this queue.  The sole writer therefore performs socket I/O only and
  cannot observe TLS state newer than the queued record. -/
  | wire (bytes : ByteArray)

structure Background where
  reader : Option (AsyncTask Unit) := none
  writer : Option (AsyncTask Unit) := none

structure Connection where
  socket : TCP.Socket.Client
  /-- `none` is plaintext.  After startup, every record transition is guarded
  by `tlsLock` and sequenced under `state`; socket I/O itself is never performed
  under either lock. -/
  tls : Option (IO.Ref Tls.Client.State)
  tlsLock : Std.Mutex Unit
  state : Std.Mutex ConnState
  outbound : Std.CloseableChannel Outbound
  notifications : Std.CloseableChannel Notification
  background : IO.Ref Background
  drained : IO.Promise Unit
  closeDone : IO.Promise Unit
  onNotice : ErrorFields → IO Unit
  host : String
  port : UInt16
  connectTimeoutMs : Nat
  /-- Retained so a fresh TLS cancellation connection cannot silently weaken
  the server-identity policy of the original connection. -/
  sslMode : SslMode := .disable
  sslRootCert : Option System.FilePath := none
  /-- BackendKeyData is immutable after startup and may be read by a fresh
  cancellation connection without touching the coordinator. -/
  cancelKey : Option Machine.BackendKey

private def sendWire (socket : TCP.Socket.Client) (bytes : ByteArray) : Async Unit := do
  if bytes.size > 0 then
    socket.send bytes

private def sendTlsFatalAlert (socket : TCP.Socket.Client)
    (state : Tls.Client.State) (error : Tls.Client.Error) : Async Unit := do
  let some description := error.fatalAlertDescription?
    | return
  match Tls.Client.sealFatalAlert state description with
  | .error _ => pure ()
  | .ok output =>
    try sendWire socket output.wireBytes catch _ => pure ()

private def recvWire (socket : TCP.Socket.Client) : Async (Option ByteArray) :=
  socket.recv? 65536

private def shutdownSocket (socket : TCP.Socket.Client) : Async Unit := do
  try socket.shutdown catch _ => pure ()

private def tlsFailure (context : String) (e : Tls.Client.Error) : IO.Error :=
  IO.userError s!"TLS {context}: {e}"

/-- Apply the libpq peer-verification policy after Finished, while the socket
is still owned by startup. The TLS engine has already strict-parsed the exact
Certificate-list bytes and verified CertificateVerify proof of possession. -/
private def verifyTlsPeer (cfg : ConnectConfig) (state : Tls.Client.State) :
    Async Unit := do
  unless (cfg.sslMode.policy).requireChain do
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
  if (cfg.sslMode.policy).requireHostname then
    match TLS13.X509.Hostname.verifyHostname cfg.host verified.leaf with
    | .ok () => pure ()
    | .error failure =>
      throw (IO.userError (toString (Error.tlsHostnameVerification failure)))

/-- Advance the TLS write sequence and return bytes ready for the socket.  This
function performs no socket I/O, so the live writer may call it under
`tlsLock` without holding that lock across an await. -/
private def sealTransportBytes (tls : Option (IO.Ref Tls.Client.State))
    (bytes : ByteArray) : IO ByteArray := do
  if bytes.isEmpty then return ByteArray.empty
  match tls with
  | none => pure bytes
  | some ref =>
    let state ← ref.get
    match Tls.Client.sealApplication state bytes with
    | .error e => throw (tlsFailure "write failed" e)
    | .ok output =>
      ref.set output.state
      pure output.wireBytes

/-- Protect and write application bytes during single-threaded startup or a
fresh cancellation connection. -/
private def sendTransport (socket : TCP.Socket.Client)
    (tls : Option (IO.Ref Tls.Client.State)) (bytes : ByteArray) : Async Unit := do
  try
    sendWire socket (← sealTransportBytes tls bytes)
  catch e =>
    shutdownSocket socket
    throw e

private inductive OpenTransportResult where
  | ok (plaintext : Option ByteArray) (reply : ByteArray)
  | error (failure : IO.Error) (alert : ByteArray)

/-- Advance the TLS read sequence.  Generated control bytes are returned to
the caller for the single writer; this function itself never writes. -/
private def openTransportBytes (tls : Option (IO.Ref Tls.Client.State))
    (chunk : ByteArray) : IO OpenTransportResult := do
  match tls with
  | none => pure (.ok (some chunk) ByteArray.empty)
  | some ref =>
    let state ← ref.get
    match Tls.Client.feedWithFailure state chunk with
    | .error failure =>
      let alert := match failure.error.fatalAlertDescription? with
        | none => ByteArray.empty
        | some description =>
          match Tls.Client.sealFatalAlert failure.state description with
          | .ok output => output.wireBytes
          | .error _ => ByteArray.empty
      pure (.error (tlsFailure "read failed" failure.error) alert)
    | .ok output =>
      ref.set output.state
      let plaintext :=
        if output.plaintext.isEmpty && output.state.closed then none
        else some output.plaintext
      pure (.ok plaintext output.wireBytes)

/-- Seal application data while its coordinator admission is sequenced, then
enqueue only socket-ready bytes.  Callers hold `conn.state`; the nested lock
order is always coordinator then TLS. -/
private def enqueueApplicationLocked (conn : Connection) (bytes : ByteArray) :
    IO (Except Error Unit) := do
  if bytes.isEmpty then return .ok ()
  try
    let wire ← conn.tlsLock.atomically do
      sealTransportBytes conn.tls bytes
    if ← conn.outbound.trySend (.wire wire) then
      pure (.ok ())
    else
      pure (.error .closed)
  catch e =>
    pure (.error (.transport (toString e)))

/-- Feed one raw socket chunk through TLS. `some #[]` means a control-only TLS
record (for example NewSessionTicket); `none` means authenticated close_notify.
Any generated control reply (currently KeyUpdate) is written before returning.
-/
private def decodeTransport (socket : TCP.Socket.Client)
    (tls : Option (IO.Ref Tls.Client.State)) (chunk : ByteArray) :
    Async (Option ByteArray) := do
  match ← openTransportBytes tls chunk with
  | .error error alert =>
      try sendWire socket alert catch _ => pure ()
      shutdownSocket socket
      throw error
  | .ok plaintext reply =>
      try sendWire socket reply catch e =>
        shutdownSocket socket
        throw e
      pure plaintext

private partial def recvTransport (socket : TCP.Socket.Client)
    (tls : Option (IO.Ref Tls.Client.State)) : Async (Option ByteArray) := do
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

private def requestOpKind? : Machine.Request → Option Machine.OpKind
  | .simpleQuery _ => some .simpleQuery
  | .parse .. => some .parse
  | .bind .. => some .bind
  | .describeStatement _ => some .describeStatement
  | .describePortal _ => some .describePortal
  | .execute .. => some .execute
  | .closeStatement _ | .closePortal _ => some .close
  | .sync => some .sync
  | .flush | .copyData _ | .copyDone | .copyFail _ | .terminate => none

private structure CompletionAction where
  promise : IO.Promise (Except Error (Array Machine.Event))
  result : Except Error (Array Machine.Event)

private structure CopyStartAction where
  promise : IO.Promise (Except Error Machine.CopyInfo)
  result : Except Error Machine.CopyInfo

private structure CopyDataAction where
  channel : Std.CloseableChannel ByteArray
  data : ByteArray

private structure RouteActions where
  completions : Array CompletionAction := #[]
  copyStarts : Array CopyStartAction := #[]
  copyData : Array CopyDataAction := #[]
  closeCopyData : Array (Std.CloseableChannel ByteArray) := #[]
  notices : Array ErrorFields := #[]
  notifications : Array Notification := #[]
  resolveDrained : Bool := false

private def eventOwner? (routing : List Machine.TaggedOp) : Option Machine.OwnerId :=
  routing.head?.map (·.owner)

/-- Route one decoded event batch without effects.  The reader applies the
returned callbacks/channel operations only after releasing the coordinator. -/
private def routeEvents (initial : ConnState) (events : Array Machine.Event) :
    ConnState × RouteActions := Id.run do
  let mut st := initial
  let mut actions : RouteActions := {}
  for ev in events do
    let before := eventOwner? st.routing
    -- NoticeResponse and NotificationResponse are connection-global.  They
    -- are valid while the pipeline is idle and must never depend on a caller
    -- being present at the head of the request queue.
    match ev with
    | .notice fields =>
      actions := { actions with notices := actions.notices.push fields }
    | .notification pid channel payload =>
      actions := { actions with notifications :=
        actions.notifications.push ⟨pid, channel, payload⟩ }
    | .parameterStatus .. => pure ()
    | _ =>
      if h : st.pending.size > 0 then
        let call := st.pending[0]
        match ev with
        | .copyInStarted info | .copyOutStarted info =>
          let call := { call with events := call.events.push ev }
          st := { st with pending := st.pending.set 0 call }
          if let some promise := call.copyStarted then
            let copyStartAction : CopyStartAction := { promise, result := .ok info }
            actions := { actions with copyStarts :=
              (actions.copyStarts.push copyStartAction) }
        | .copyData data =>
          -- A call with a streaming sink receives payloads through its
          -- channel only; also retaining them in the completion events would
          -- buffer the whole COPY TO STDOUT payload until the call completes,
          -- defeating the sink.  Calls without a channel keep the events.
          match call.copyData with
          | some channel =>
            let copyDataAction : CopyDataAction := { channel, data }
            actions := { actions with copyData :=
              (actions.copyData.push copyDataAction) }
          | none =>
            let call := { call with events := call.events.push ev }
            st := { st with pending := st.pending.set 0 call }
        | _ =>
          let call := { call with events := call.events.push ev }
          st := { st with pending := st.pending.set 0 call }
    st := { st with routing := Machine.taggedStep st.routing ev }
    let after := eventOwner? st.routing
    if before != after then
      if h : st.pending.size > 0 then
        let call := st.pending[0]
        let completionAction : CompletionAction := {
          promise := call.completion, result := .ok call.events }
        actions := { actions with completions :=
          (actions.completions.push completionAction) }
        if let some promise := call.copyStarted then
          let copyStartAction : CopyStartAction := { promise, result :=
            (Except.error (.rejected (.rejectedInvalid
              "statement did not enter the requested COPY mode"))) }
          actions := { actions with copyStarts :=
            (actions.copyStarts.push copyStartAction) }
        if let some channel := call.copyData then
          actions := { actions with closeCopyData :=
            (actions.closeCopyData.push channel) }
        st := { st with
          pending := st.pending.extract 1 st.pending.size
          exclusiveOwner :=
            if st.exclusiveOwner == some call.owner then none else st.exclusiveOwner }
  if st.life == .closing && st.pending.isEmpty then
    actions := { actions with resolveDrained := true }
  return (st, actions)

private def applyRouteActions (conn : Connection) (actions : RouteActions) : IO Unit := do
  for action in actions.completions do
    discard <| action.promise.resolve action.result
  for action in actions.copyStarts do
    discard <| action.promise.resolve action.result
  for action in actions.copyData do
    discard <| action.channel.trySend action.data
  for channel in actions.closeCopyData do
    discard <| channel.close.toBaseIO
  for fields in actions.notices do
    conn.onNotice fields
  for notification in actions.notifications do
    discard <| conn.notifications.trySend notification
  if actions.resolveDrained then
    discard <| conn.drained.resolve ()

private def failedState (st : ConnState) : ConnState :=
  { st with life := .closed, routing := [], pending := #[], exclusiveOwner := none }

/-- Apply failure effects after the coordinator has atomically detached every
pending caller. -/
private def finishFailure (conn : Connection) (error : Error)
    (calls : Array PendingCall) : IO Unit := do
  for call in calls do
    discard <| call.completion.resolve (.error error)
    if let some promise := call.copyStarted then
      discard <| promise.resolve (.error error)
    if let some channel := call.copyData then
      discard <| channel.close.toBaseIO
  discard <| conn.drained.resolve ()
  discard <| conn.closeDone.resolve ()
  discard <| conn.notifications.close.toBaseIO
  discard <| conn.outbound.close.toBaseIO

private def failConnection (conn : Connection) (error : Error) : IO Unit := do
  let calls ← conn.state.atomically do
    let st ← get
    if st.life == .closed then
      pure (#[] : Array PendingCall)
    else
      set (failedState st)
      pure st.pending
  finishFailure conn error calls

private partial def writerLoop (conn : Connection) : Async Unit := do
  match ← await (← conn.outbound.recv) with
  | none => pure ()
  | some (.wire wire) =>
    try
      sendWire conn.socket wire
      writerLoop conn
    catch e =>
      failConnection conn (.transport (toString e))
      try conn.socket.shutdown catch _ => pure ()

private inductive ReaderOutcome where
  | stop
  | failed (error : Error) (calls : Array PendingCall)
  | continued (actions : Option RouteActions)

private partial def readerLoop (conn : Connection) : Async Unit := do
  try
    match ← recvWire conn.socket with
    | none =>
      let cleanTlsEof ← conn.tlsLock.atomically do
        match conn.tls with
        | none => pure true
        | some ref => pure (← ref.get).peerClosed
      failConnection conn (if cleanTlsEof then .disconnected
        else .transport "TLS connection closed without close_notify")
    | some wireChunk =>
      -- The coordinator orders TLS read transitions, generated TLS replies,
      -- application sealing, and writer-queue insertion.  In particular a
      -- KeyUpdate reply is queued before any caller can seal later data.
      let outcome ← conn.state.atomically do
        let st ← get
        if st.life == .closed then
          pure ReaderOutcome.stop
        else
          let opened ← conn.tlsLock.atomically do
            openTransportBytes conn.tls wireChunk
          match opened with
          | .error error alert =>
            unless alert.isEmpty do discard <| conn.outbound.trySend (.wire alert)
            set (failedState st)
            pure (.failed (.transport (toString error)) st.pending)
          | .ok plaintext tlsReply =>
            if !tlsReply.isEmpty && !(← conn.outbound.trySend (.wire tlsReply)) then
              set (failedState st)
              pure (.failed .closed st.pending)
            else
              match plaintext with
              | none =>
                -- The TLS engine models half-close explicitly. PostgreSQL has
                -- no useful work after the peer closes its write direction,
                -- so reciprocate under the same ordering critical section.
                let closeWire ← conn.tlsLock.atomically do
                  match conn.tls with
                  | none => pure ByteArray.empty
                  | some ref =>
                    match Tls.Client.closeNotify (← ref.get) with
                    | .error _ => pure ByteArray.empty
                    | .ok output =>
                      ref.set output.state
                      pure output.wireBytes
                unless closeWire.isEmpty do
                  discard <| conn.outbound.trySend (.wire closeWire)
                set (failedState st)
                pure (.failed .disconnected st.pending)
              | some chunk =>
                if chunk.isEmpty then
                  pure (.continued none)
                else
                  match Machine.feed st.machine chunk with
                  | .error e =>
                    set (failedState st)
                    pure (.failed (.fatal e) st.pending)
                  | .ok (machine, events, out) =>
                    let (next, actions) := routeEvents { st with machine } events
                    match ← enqueueApplicationLocked conn out with
                    | .error error =>
                      set (failedState st)
                      pure (.failed error st.pending)
                    | .ok () =>
                      set next
                      pure (.continued (some actions))
      match outcome with
      | .stop => pure ()
      | .failed error calls =>
        finishFailure conn error calls
        -- `finishFailure` closes the queue, so the sole writer can flush a
        -- queued TLS alert/close_notify before the socket is torn down.
        if let some writer := (← conn.background.get).writer then
          try
            discard <| Async.race (Async.ofAsyncTask writer)
              (Std.Async.sleep (Std.Time.Millisecond.Offset.ofNat 1000))
          catch _ => pure ()
        try conn.socket.shutdown catch _ => pure ()
      | .continued none => readerLoop conn
      | .continued (some actions) =>
        applyRouteActions conn actions
        readerLoop conn
  catch e =>
    failConnection conn (.transport (toString e))
    try conn.socket.shutdown catch _ => pure ()

private def startBackgroundTasks (conn : Connection) : IO Unit := do
  let writer ← Async.toIO (writerLoop conn)
  conn.background.set { writer := some writer }
  let reader ← Async.toIO (readerLoop conn)
  conn.background.set { reader := some reader, writer := some writer }

private def toSocketAddress (addr : Std.Net.IPAddr) (port : UInt16) : Std.Net.SocketAddress :=
  match addr with
  | .v4 a => .v4 { addr := a, port }
  | .v6 a => .v6 { addr := a, port }

/-- Run `act` with a cooperative relative timeout; `none` on timeout.  Neither
branch occupies a worker while waiting. -/
private def timedIO (ms : Nat) (act : Async α) : Async (Option α) := do
  if ms == 0 then
    some <$> act
  else
    Async.race (some <$> act) do
      Std.Async.sleep (Std.Time.Millisecond.Offset.ofNat ms)
      pure none

private def deadlineFromNow (ms : Nat) : Async (Option Nat) := do
  if ms == 0 then
    pure none
  else
    pure (some ((← IO.monoNanosNow) + ms * 1000000))

private def timedIOUntil (deadline : Option Nat) (act : Async α) : Async (Option α) := do
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
    Async UInt8 := do
  let some response? ← timedIOUntil deadline (socket.recv? 1)
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
    Async (IO.Ref Tls.Client.State) := do
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

/-- The transport an individual connection attempt uses. -/
inductive ConnectPolicy where
  | plaintext
  | negotiateTls (required : Bool)
  deriving Repr, BEq, DecidableEq, Inhabited

/-- The transport a mode attempts first — read straight off `SslMode.policy`
(`initialAttempt_of_requireEncryption`). -/
def SslMode.initialAttempt : SslMode → ConnectPolicy
  | .disable => .plaintext
  | .allow => .plaintext
  | .prefer => .negotiateTls false
  | .require => .negotiateTls true
  | .verifyCa => .negotiateTls true
  | .verifyFull => .negotiateTls true

/-- The transport a mode may retry with after the server rejects its first
attempt — `none` for every mode that requires encryption
(`fallbackAttempt_of_requireEncryption`). -/
def SslMode.fallbackAttempt : SslMode → Option ConnectPolicy
  | .allow => some (.negotiateTls true)
  | .prefer => some .plaintext
  | _ => none

private def negotiateTransport (socket : TCP.Socket.Client) (cfg : ConnectConfig)
    (policy : ConnectPolicy) (deadline : Option Nat) :
    Async (Option (IO.Ref Tls.Client.State)) := do
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

private def connectSocket (host : String) (port : UInt16) : Async TCP.Socket.Client := do
  let addrs ← DNS.getAddrInfo host (toString port.toNat)
  if addrs.isEmpty then
    throw (IO.userError s!"could not resolve {host}")
  let mut lastError : Option IO.Error := none
  for addr in addrs do
    let socket ← TCP.Socket.Client.mk
    try
      socket.connect (toSocketAddress addr port)
      socket.noDelay
      return socket
    catch e =>
      lastError := some e
  throw (lastError.getD (IO.userError s!"could not connect to {host}:{port.toNat}"))

private def connectAttempt (cfg : ConnectConfig) (onNotice : ErrorFields → IO Unit)
    (policy : ConnectPolicy) : Async (Except Machine.PgError Connection) := do
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
    let state ← Std.Mutex.new { machine := m }
    let conn : Connection := {
      socket, tls, state, onNotice, host := cfg.host, port := cfg.port
      tlsLock := ← Std.Mutex.new ()
      outbound := ← Std.CloseableChannel.new
      notifications := ← Std.CloseableChannel.new
      background := ← IO.mkRef {}
      drained := ← IO.Promise.new
      closeDone := ← IO.Promise.new
      connectTimeoutMs := cfg.connectTimeoutMs
      sslMode := cfg.sslMode
      sslRootCert := cfg.sslRootCert
      cancelKey := m.cancelKey? }
    for notification in notifications do
      discard <| conn.notifications.trySend notification
    startBackgroundTasks conn
    pure (.ok conn)
  catch e =>
    shutdownSocket socket
    throw e

private def indicatesTlsRequired (fields : ErrorFields) : Bool :=
  fields.sqlState? == some "28000" &&
    (fields.message?.map (·.endsWith "no encryption")).getD false

private def indicatesTlsRejected (fields : ErrorFields) : Bool :=
  fields.sqlState? == some "28000" &&
    (fields.message?.map (·.endsWith "SSL encryption")).getD false

/-- The server error that licenses a mode's retry: `prefer` retries in
plaintext when the server rejected SSL, `allow` retries with TLS when the
server demanded encryption. Modes without a fallback never retry. -/
def SslMode.fallbackTriggered : SslMode → ErrorFields → Bool
  | .prefer, fields => indicatesTlsRejected fields
  | .allow, fields => indicatesTlsRequired fields
  | _, _ => false

/-!
### Transport-policy laws

`connect` makes exactly two decisions — which transport to attempt, and
whether to retry — and both are these pure tables, so the guarantees of
`SslMode.policy` carry into the connect path.
-/

/-- A mode that requires encryption demands TLS on its first attempt. -/
theorem initialAttempt_of_requireEncryption {m : SslMode}
    (h : (m.policy).requireEncryption = true) :
    m.initialAttempt = .negotiateTls true := by
  cases m <;> first | rfl | exact absurd h (by decide)

/-- **No insecure fallback in the connect path**: a mode that requires
encryption has no retry at all, so no failure can downgrade it to plaintext. -/
theorem fallbackAttempt_of_requireEncryption {m : SslMode}
    (h : (m.policy).requireEncryption = true) : m.fallbackAttempt = none := by
  cases m <;> first | rfl | exact absurd h (by decide)

/-- The retry table agrees with the policy table. -/
theorem fallbackAttempt_isSome (m : SslMode) :
    (m.fallbackAttempt).isSome = (m.policy).allowsFallback := by
  cases m <;> rfl

/-- Nothing is ever retried for a mode with no fallback. -/
theorem fallbackTriggered_of_no_fallback {m : SslMode}
    (h : m.fallbackAttempt = none) (fields : ErrorFields) :
    m.fallbackTriggered fields = false := by
  cases m <;> first | rfl | exact absurd h (by simp [SslMode.fallbackAttempt])

/-- A retry never gives up encryption a mode already achieved: the only
plaintext fallback belongs to `prefer`, which does not require encryption. -/
theorem fallback_plaintext_only_unencrypted {m : SslMode}
    (h : m.fallbackAttempt = some .plaintext) :
    (m.policy).requireEncryption = false := by
  cases m <;> first | rfl | exact absurd h (by simp [SslMode.fallbackAttempt])

private def finishConnectAttempt (result : Except Machine.PgError Connection) :
    Async Connection :=
  match result with
  | .ok conn => pure conn
  | .error (.channelBinding failure) =>
    throw (IO.userError (toString (Error.channelBinding failure)))
  | .error e => throw (IO.userError (toString (Error.fatal e)))

/-- Connect and authenticate. `require` encrypts and verifies CertificateVerify
proof of possession but deliberately does not validate certificate identity.
`verify-ca` additionally validates a path to the configured trust store;
`verify-full` also verifies the connection hostname. Fatal problems throw
`IO.Error`; `onNotice` receives server notices for the connection lifetime.

Both transport decisions come from the pure tables `SslMode.initialAttempt`
and `SslMode.fallbackAttempt`, which are proved to follow `SslMode.policy` —
in particular no encryption-requiring mode has any retry
(`fallbackAttempt_of_requireEncryption`). -/
def connect (cfg : ConnectConfig) (onNotice : ErrorFields → IO Unit := fun _ => pure ()) :
    Async Connection := do
  match ← connectAttempt cfg onNotice cfg.sslMode.initialAttempt with
  | .ok conn => pure conn
  | .error e =>
    match cfg.sslMode.fallbackAttempt with
    | none => finishConnectAttempt (.error e)
    | some fallback =>
      match e with
      | .serverFatal fields =>
        if cfg.sslMode.fallbackTriggered fields then
          finishConnectAttempt (← connectAttempt cfg onNotice fallback)
        else
          finishConnectAttempt (.error e)
      | _ => finishConnectAttempt (.error e)

/-- Connect from a `postgres://` URL. -/
def connectUri (uri : String) (onNotice : ErrorFields → IO Unit := fun _ => pure ()) :
    Async Connection := do
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

private def rejected (message : String) : Error :=
  .rejected (.rejectedInvalid message)

private def isBoundary : Machine.Request → Bool
  | .sync | .simpleQuery _ => true
  | _ => false

private def isRunControl : Machine.Request → Bool
  | .flush | .copyData _ | .copyDone | .copyFail _ | .terminate => true
  | _ => false

private def validateRun (reqs : Array Machine.Request) : Except Error (List Machine.OpKind) := do
  if reqs.isEmpty then
    throw (rejected "run needs a non-empty request batch")
  if reqs.size > 1024 then
    throw (rejected "run batch exceeds the 1024-request safety limit")
  let some final := reqs.back?
    | throw (rejected "run needs a non-empty request batch")
  unless isBoundary final do
    throw (rejected "run needs a final sync or simpleQuery boundary")
  for req in reqs.extract 0 (reqs.size - 1) do
    if isBoundary req then
      throw (rejected "run does not allow requests after a response boundary")
    if isRunControl req then
      throw (rejected "run does not accept COPY, Flush, or Terminate control requests")
  if isRunControl final then
    throw (rejected "run does not accept COPY, Flush, or Terminate control requests")
  -- A simple query must be the entire batch.  Extended-protocol error
  -- recovery skips to the batch's own Sync (`Machine.taggedDropUntilSync`
  -- stops only at `OpKind.sync`), so a Query boundary after extended requests
  -- would let recovery drop past this owner's batch into later owners' ops,
  -- misattributing their completions.  Admitting only sync-terminated
  -- extended batches is what makes recovery owner-local
  -- (`Machine.taggedStep_error_stays_in_batch`).
  if (final matches Machine.Request.simpleQuery _) && reqs.size != 1 then
    throw (rejected
      "run does not allow extended requests before a simpleQuery boundary; end extended batches with sync")
  pure (reqs.toList.filterMap requestOpKind?)

private structure CallHandle where
  owner : Machine.OwnerId
  completion : IO.Promise (Except Error (Array Machine.Event))
  copyStarted : Option (IO.Promise (Except Error Machine.CopyInfo)) := none
  copyData : Option (Std.CloseableChannel ByteArray) := none

private inductive CoordinatorResult (α : Type) where
  | rejected (error : Error)
  | failed (error : Error) (calls : Array PendingCall)
  | ok (value : α)

private def submitBatch (conn : Connection) (reqs : Array Machine.Request)
    (exclusive : Bool := false)
    (copyStarted : Option (IO.Promise (Except Error Machine.CopyInfo)) := none)
    (copyData : Option (Std.CloseableChannel ByteArray) := none) :
    Async (Except Error CallHandle) := do
  let kinds ← match validateRun reqs with
    | .ok kinds => pure kinds
    | .error e => return .error e
  let completion ← IO.Promise.new
  let submitted : CoordinatorResult Machine.OwnerId ← conn.state.atomically do
    let st ← get
    match st.life with
    | .closing | .closed => pure (.rejected Error.closed)
    | .open =>
      if st.exclusiveOwner.isSome then
        pure (.rejected (rejected "a COPY operation owns the connection"))
      else
        match Machine.submitAll st.machine reqs with
        | .error e => pure (.rejected (.rejected e))
        | .ok (machine, bytes) =>
          let owner := st.nextOwner
          let tagged := kinds.map fun kind => ({ owner, kind } : Machine.TaggedOp)
          let call : PendingCall := {
            owner, completion, copyStarted, copyData }
          -- Admission order, owner order, and writer-queue order are one
          -- transaction.  `trySend` is nonblocking, so no peer wait occurs
          -- while the coordinator is held.
          match ← enqueueApplicationLocked conn bytes with
          | .error error =>
            set (failedState st)
            pure (.failed error st.pending)
          | .ok () =>
            set { st with
              machine
              routing := st.routing ++ tagged
              pending := st.pending.push call
              nextOwner := owner + 1
              exclusiveOwner := if exclusive then some owner else none }
            pure (.ok owner)
  match submitted with
  | .rejected e => pure (.error e)
  | .failed e calls =>
    finishFailure conn e calls
    pure (.error e)
  | .ok owner => pure (.ok { owner, completion, copyStarted, copyData })

private def submitCopyControl (conn : Connection) (owner : Machine.OwnerId)
    (request : Machine.Request) : Async (Except Error Unit) := do
  let submitted : CoordinatorResult Unit ← conn.state.atomically do
    let st ← get
    if st.life == .closed then
      pure (.rejected Error.closed)
    else if st.exclusiveOwner != some owner then
      pure (.rejected (rejected "COPY ownership is no longer active"))
    else
      match Machine.submit st.machine request with
      | .error e => pure (.rejected (.rejected e))
      | .ok (machine, bytes) =>
        match ← enqueueApplicationLocked conn bytes with
        | .error error =>
          set (failedState st)
          pure (.failed error st.pending)
        | .ok () =>
          set { st with machine }
          pure (.ok ())
  match submitted with
  | .rejected e => pure (.error e)
  | .failed e calls =>
    finishFailure conn e calls
    pure (.error e)
  | .ok () => pure (.ok ())

/-- Submit one bounded batch.  Batches are admitted concurrently and written
in submission order.  Each batch must have exactly one final ReadyForQuery
boundary; protocol-control traffic is reserved for the dedicated COPY/close
paths. -/
def run (conn : Connection) (reqs : Array Machine.Request) :
    Async (Except Error (Array Machine.Event)) := do
  match ← submitBatch conn reqs with
  | .error e => pure (.error e)
  | .ok call => await call.completion

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

def query (conn : Connection) (sql : String) : Async (Except Error (Array Rows)) := do
  pure ((← conn.run #[.simpleQuery sql]).bind foldSimple)

def exec (conn : Connection) (sql : String) : Async (Except Error (Array String)) := do
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

def prepare (conn : Connection) (name sql : String) (paramTypeOids : Array UInt32 := #[]) :
    Async (Except Error Statement) := do
  pure ((← conn.run #[.parse name sql paramTypeOids, .describeStatement name, .sync]).bind
    (foldPrepare name))

def execute (conn : Connection) (statement : String)
    (params : Array (Option ByteArray) := #[])
    (paramFormats : Array UInt16 := #[])
    (resultFormats : Array UInt16 := #[]) : Async (Except Error Rows) := do
  pure ((← conn.run #[
    .bind "" statement paramFormats params resultFormats,
    .describePortal "",
    .execute "" 0,
    .sync]).bind foldExecute)

private inductive NotificationWait where
  | received (notification : Option Notification)
  | timeout

/-- Await one notification without competing with the connection reader for
socket ownership. -/
def waitNotification (conn : Connection) (timeoutMs : Nat := 1000) :
    Async (Except Error (Option Notification)) := do
  let sleep ← Sleep.mk (Std.Time.Millisecond.Offset.ofNat timeoutMs)
  let event ← Selectable.one #[
    .case conn.notifications.recvSelector
      (fun item => pure (NotificationWait.received item)),
    .case sleep.selector (fun _ => pure NotificationWait.timeout)]
  match event with
  | .timeout => pure (.ok none)
  | .received (some notification) => pure (.ok (some notification))
  | .received none =>
    let closed ← conn.state.atomically do pure ((← get).life != .open)
    pure (.error (if closed then .closed else .disconnected))

private def firstServerError (events : Array Machine.Event) : Option ErrorFields :=
  events.findSome? fun
    | .errorResponse fields => some fields
    | _ => none

private def commandTag (events : Array Machine.Event) : String :=
  (events.findSome? fun
    | .commandComplete tag => some tag
    | _ => none).getD ""

/-- `COPY ... FROM STDIN`.  The producer is cooperative and runs outside the
reader/coordinator; an exception submits best-effort CopyFail before the final
ReadyForQuery is awaited. -/
def copyIn (conn : Connection) (sql : String)
    (next : Async (Option ByteArray)) : Async (Except Error String) := do
  let started ← IO.Promise.new
  let call ← match ← submitBatch conn #[.simpleQuery sql] true (some started) with
    | .error e => return .error e
    | .ok call => pure call
  match ← await started with
  | .error e => pure (.error e)
  | .ok _ =>
    let mut producerFailure : Option String := none
    let mut done := false
    while !done do
      let chunk? ← try next catch e =>
        producerFailure := some (toString e)
        pure none
      match chunk? with
      | some chunk =>
        match ← submitCopyControl conn call.owner (.copyData chunk) with
        | .ok () => pure ()
        | .error e => return .error e
      | none => done := true
    let finish := match producerFailure with
      | some reason => Machine.Request.copyFail reason
      | none => Machine.Request.copyDone
    match ← submitCopyControl conn call.owner finish with
    | .error e => pure (.error e)
    | .ok () =>
      match ← await call.completion with
      | .error e => pure (.error e)
      | .ok events =>
        match firstServerError events with
        | some fields => pure (.error (.server fields))
        | none => pure (.ok (commandTag events))

def copyInChunks (conn : Connection) (sql : String) (chunks : Array ByteArray) :
    Async (Except Error String) := do
  let idx ← IO.mkRef 0
  conn.copyIn sql do
    let i ← idx.get
    if h : i < chunks.size then
      idx.set (i + 1)
      pure (some chunks[i])
    else
      pure none

private partial def pumpCopyOut (channel : Std.CloseableChannel ByteArray)
    (sink : ByteArray → Async Unit) : Async Unit := do
  match ← await (← channel.recv) with
  | none => pure ()
  | some data => sink data; pumpCopyOut channel sink

/-- `COPY ... TO STDOUT`.  The reader only routes chunks; the caller's sink is
run by this independent cooperative pump. -/
def copyOut (conn : Connection) (sql : String) (sink : ByteArray → Async Unit) :
    Async (Except Error String) := do
  let started ← IO.Promise.new
  let data ← Std.CloseableChannel.new
  let call ← match ← submitBatch conn #[.simpleQuery sql] true (some started) (some data) with
    | .error e => return .error e
    | .ok call => pure call
  match ← await started with
  | .error e => pure (.error e)
  | .ok _ =>
    pumpCopyOut data sink
    match ← await call.completion with
    | .error e => pure (.error e)
    | .ok events =>
      match firstServerError events with
      | some fields => pure (.error (.server fields))
      | none => pure (.ok (commandTag events))

def listen (conn : Connection) (channel : String) : Async (Except Error Unit) := do
  let quoted := "\"" ++ channel.replace "\"" "\"\"" ++ "\""
  pure ((← conn.exec s!"LISTEN {quoted}").map (fun _ => ()))

def notify (conn : Connection) (channel payload : String) : Async (Except Error Unit) := do
  let r ← conn.run #[
    .parse "" "SELECT pg_notify($1, $2)",
    .bind "" "" #[] #[some channel.toUTF8, some payload.toUTF8] #[],
    .execute "" 0,
    .sync]
  pure (r.bind fun events =>
    match firstServerError events with
    | some fields => .error (.server fields)
    | none => .ok ())

/-- Dispatch PostgreSQL CancelRequest on its policy-equivalent fresh
connection.  It never consumes the main connection's reader or writer. -/
def cancel (conn : Connection) : Async Unit := do
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
      let tls ← if conn.tls.isSome then
          negotiateTransport socket cancelCfg (.negotiateTls true) deadline
        else pure none
      sendTransport socket tls (encodeCancelRequest key.processId key.secret)
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

def parameter? (conn : Connection) (name : String) : Async (Option String) :=
  conn.state.atomically do pure ((← get).machine.parameter? name)

def protocolVersion (conn : Connection) : Async Machine.ProtocolVersion :=
  conn.state.atomically do pure (← get).machine.protocolVersion

def negotiatedSaslMechanism? (conn : Connection) : Async (Option String) :=
  conn.state.atomically do pure (← get).machine.negotiatedSaslMechanism?

def usesTls (conn : Connection) : Bool := conn.tls.isSome

def peerCertificate? (conn : Connection) : Async (Option ByteArray) := do
  conn.tlsLock.atomically do
    match conn.tls with
    | none => pure none
    | some ref => pure (← ref.get).leafCertificate?

/-- Idempotent graceful shutdown.  The leader rejects new work, waits for all
already-attributed calls, enqueues one Terminate and (for TLS) close_notify,
drains the exact writer task, then half-closes the socket. -/
def close (conn : Connection) : Async Unit := do
  let (leader, drainNow) ← conn.state.atomically do
    let st ← get
    match st.life with
    | .open =>
      set { st with life := .closing }
      pure (true, st.pending.isEmpty)
    | .closing => pure (false, false)
    | .closed => pure (false, false)
  if !leader then
    discard <| await conn.closeDone
    return
  if drainNow then discard <| conn.drained.resolve ()
  discard <| await conn.drained
  let closeFailure? ← conn.state.atomically do
    let st ← get
    if st.life == .closed then pure none
    else
      let (machine, terminateBytes) :=
        match Machine.submit st.machine .terminate with
        | .error _ => (st.machine, ByteArray.empty)
        | .ok result => result
      match ← enqueueApplicationLocked conn terminateBytes with
      | .error error =>
        set (failedState st)
        pure (some (error, st.pending))
      | .ok () =>
        -- Every earlier application item is already sealed and ahead of
        -- Terminate in the writer FIFO.  Advancing TLS to close_notify here
        -- therefore cannot invalidate a deferred application seal.
        let closeWire ← conn.tlsLock.atomically do
          match conn.tls with
          | none => pure ByteArray.empty
          | some ref =>
            match Tls.Client.closeNotify (← ref.get) with
            | .error _ => pure ByteArray.empty
            | .ok output => ref.set output.state; pure output.wireBytes
        if !closeWire.isEmpty && !(← conn.outbound.trySend (.wire closeWire)) then
          set (failedState st)
          pure (some (Error.closed, st.pending))
        else
          set { st with machine }
          pure none
  if let some (error, calls) := closeFailure? then
    finishFailure conn error calls
  discard <| conn.outbound.close.toBaseIO
  if let some writer := (← conn.background.get).writer then
    try
      discard <| Async.race (Async.ofAsyncTask writer)
        (Std.Async.sleep (Std.Time.Millisecond.Offset.ofNat 1000))
    catch _ => pure ()
  conn.state.atomically do modify fun st => { st with life := .closed }
  discard <| conn.notifications.close.toBaseIO
  try
    discard <| Async.race conn.socket.shutdown
      (Std.Async.sleep (Std.Time.Millisecond.Offset.ofNat 1000))
  catch _ => pure ()
  if let some reader := (← conn.background.get).reader then
    try
      discard <| Async.race (Async.ofAsyncTask reader)
        (Std.Async.sleep (Std.Time.Millisecond.Offset.ofNat 1000))
    catch _ => pure ()
  discard <| conn.closeDone.resolve ()

end Connection

end Pg
