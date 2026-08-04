module

public import Pg.Protocol.Message
public import Pg.Protocol.Backend
public import Pg.Protocol.Frontend
public import Pg.Sasl.Scram
public import Pg.Crypto.Md5
public import Pg.ChannelBinding

public section

namespace Pg
namespace Protocol
namespace Machine

/-!
The sans-IO connection state machine. Pure: the IO shell feeds it TCP chunks
(`feed`) or framed messages (`step`) and user requests (`submit`), and writes
whatever bytes come back.

Contracts:
- `step`/`feed` failure (`Except.error`) means the connection is **poisoned**
  — there is no new state to continue with, by construction. Close the socket.
- Recoverable server errors are **events** (`Event.errorResponse`), never
  `step` failures; the machine transitions into the protocol's drain/abort
  recovery internally.
- `submit` failure is a **rejection**: the state is unchanged and the
  connection remains healthy (`rejectedInvalid` for caller bugs,
  `rejectedAborted` while an extended-protocol error awaits its Sync).

Correlation: events are a flat stream in wire order. Backend replies arrive
in exactly the order requests were sent, so the shell keeps its own FIFO of
user-facing completions and pops on terminal events (`ready` for
sync/simpleQuery, `commandComplete`/`portalSuspended`/`emptyQuery` for
execute, ...). `dropAborted` is exported so the shell applies the same
error-recovery drop rule the machine applies internally.
-/

inductive ProtocolVersion where
  | v3_0
  | v3_2
  deriving Repr, BEq, Inhabited

structure Config where
  user : String
  database : Option String := none
  password : Option String := none
  /-- Extra startup parameters (application_name, ...). `user`, `database`,
  and `client_encoding` here are ignored — the dedicated fields win and
  UTF-8 is always requested. -/
  parameters : Array (String × String) := #[]
  requestedVersion : ProtocolVersion := .v3_0
  /-- Fresh entropy per connection (`Sasl.Scram.genNonce`); the machine is
  pure and cannot draw its own. Reuse across connections is a security bug. -/
  scramNonce : String := "!"
  /-- libpq-compatible SCRAM channel-binding policy. -/
  channelBinding : ChannelBindingMode := .prefer
  /-- RFC 5929 `tls-server-end-point` data for this connection's negotiated
  TLS leaf certificate. `none` means the transport is plaintext. -/
  tlsServerEndPoint : Option ByteArray := none
  deriving Repr, Inhabited

structure BackendKey where
  processId : UInt32
  /-- 4 bytes under protocol 3.0; 1–256 bytes under 3.2. -/
  secret : ByteArray
  deriving Repr, BEq, Inhabited

inductive AuthState where
  | awaitingRequest
  | sentCleartext
  | sentMd5
  | scram (client : Sasl.Scram.Client)
  | saslDone
  /-- AuthenticationOk seen; draining ParameterStatus/BackendKeyData until the
  first ReadyForQuery. -/
  | awaitingReady
  deriving Inhabited

inductive OpKind where
  | parse
  | bind
  | describeStatement
  | describePortal
  | close
  | execute
  | sync
  | simpleQuery
  deriving Repr, BEq, Inhabited

structure CopyInfo where
  binary : Bool
  columnFormats : Array UInt16
  deriving Repr, BEq, Inhabited

/-- Reply progress of the op at the head of the pipeline. -/
inductive Progress where
  | start
  /-- describeStatement: ParameterDescription consumed, awaiting
  RowDescription | NoData. -/
  | descParams
  /-- Streaming DataRows; column count known when a RowDescription led (simple
  query), unknown for Execute (the portal was described separately). -/
  | rows (cols : Option Nat)
  | copyIn (info : CopyInfo) (doneSent : Bool)
  | copyOut (info : CopyInfo)
  /-- Error seen; only async messages until this op's terminal message. -/
  | drainError
  deriving Repr, BEq, Inhabited

structure CurrentOp where
  kind : OpKind
  progress : Progress := .start
  deriving Repr, BEq, Inhabited

structure Pipeline where
  current : Option CurrentOp := none
  queued : Array OpKind := #[]
  /-- Extended-protocol error seen with no Sync in flight (Flush-driven use):
  the backend discards messages until a Sync arrives, so submits are gated
  (`rejectedAborted`) until the user supplies one. -/
  aborted : Bool := false
  deriving Repr, Inhabited

inductive Phase where
  | startup (auth : AuthState)
  /-- Post-auth. "Ready" is simply an empty pipeline. -/
  | running (pipe : Pipeline)
  | closed
  deriving Inhabited

structure State where
  cfg : Config
  phase : Phase
  decode : DecodeState := {}
  txStatus : TxStatus := .idle
  params : Array (String × String) := #[]
  backendKey : Option BackendKey := none
  protocolVersion : ProtocolVersion := .v3_0
  /-- SASL mechanism selected during authentication, retained for diagnostics
  and live security assertions. -/
  negotiatedSaslMechanism : Option String := none
  deriving Inhabited

inductive Event where
  | authOk
  | negotiatedVersion (version : ProtocolVersion) (unrecognizedOptions : Array String)
  | parameterStatus (name value : String)
  /-- ReadyForQuery — the correlation marker ending a sync/simpleQuery cycle. -/
  | ready (tx : TxStatus)
  | parseComplete
  | bindComplete
  | closeComplete
  | noData
  | parameterDescription (typeOids : Array UInt32)
  | rowDescription (columns : Array ColumnDesc)
  | dataRow (columns : Array (Option ByteArray))
  | commandComplete (tag : String)
  | emptyQuery
  | portalSuspended
  /-- Recoverable server error (the connection stays usable). -/
  | errorResponse (fields : ErrorFields)
  | notice (fields : ErrorFields)
  | notification (processId : UInt32) (channel payload : String)
  | copyInStarted (info : CopyInfo)
  | copyOutStarted (info : CopyInfo)
  | copyData (data : ByteArray)
  | copyOutDone
  deriving Repr, BEq, Inhabited

inductive PgError where
  -- fatal (step/feed): connection poisoned
  | decode (message : String)
  | protocol (message : String)
  /-- ErrorResponse with no recovery path: during startup, or unsolicited
  while quiescent (e.g. 57P01 admin shutdown). -/
  | serverFatal (fields : ErrorFields)
  | authFailed (why : String)
  | unsupportedAuth (method : String)
  | missingPassword
  | channelBinding (failure : ChannelBindingFailure)
  -- rejections (submit): state unchanged, connection healthy
  | rejectedInvalid (why : String)
  | rejectedAborted
  deriving Repr, BEq, Inhabited

inductive Request where
  | simpleQuery (sql : String)
  | parse (name sql : String) (paramTypeOids : Array UInt32 := #[])
  | bind (portal statement : String) (paramFormats : Array UInt16 := #[])
      (params : Array (Option ByteArray) := #[]) (resultFormats : Array UInt16 := #[])
  | describeStatement (name : String)
  | describePortal (name : String)
  | execute (portal : String) (maxRows : UInt32 := 0)
  | closeStatement (name : String)
  | closePortal (name : String)
  | flush
  | sync
  | copyData (data : ByteArray)
  | copyDone
  | copyFail (reason : String)
  | terminate
  deriving Repr, Inhabited

/-- Drop queue entries up to (but excluding) the first Sync — the set of
expectations an extended-protocol error cancels. Returns the remainder
(starting at the Sync when one was found) and whether one was found. Exported
so the IO shell applies the identical rule to its completion FIFO. -/
def dropAborted (isSync : α → Bool) (queue : Array α) : Array α × Bool :=
  match queue.findIdx? isSync with
  | some i => (queue.extract i queue.size, true)
  | none => (#[], false)

def State.isQuiescent (s : State) : Bool :=
  match s.phase with
  | .running pipe => pipe.current.isNone && pipe.queued.isEmpty && !pipe.aborted
  | _ => false

/-- Latest backend-reported value of a run-time parameter (ParameterStatus). -/
def State.parameter? (s : State) (name : String) : Option String :=
  (s.params.find? (·.1 == name)).map (·.2)

/-- Key for building a CancelRequest on a separate connection. -/
def State.cancelKey? (s : State) : Option BackendKey := s.backendKey

/-- SASL mechanism negotiated on this connection, once the server has sent
its AuthenticationSASL mechanism list. -/
def State.negotiatedSaslMechanism? (s : State) : Option String :=
  s.negotiatedSaslMechanism

/-- Select the SCRAM GS2 channel-binding flag from transport state, client
policy, and the server's unmodified mechanism advertisement.

The `y` downgrade signal is emitted only for TLS + `prefer` + base SCRAM
without PLUS. Normal plaintext SCRAM uses `n` (a TLS-only PLUS advertisement
on plaintext is rejected); an offered PLUS mechanism over TLS always wins
under `prefer`; `disable` always uses base SCRAM. -/
def selectScramChannelBinding (mode : ChannelBindingMode)
    (tlsServerEndPoint : Option ByteArray) (mechanisms : Array String) :
    Except ChannelBindingFailure Sasl.Scram.ChannelBinding := do
  let offersBase := mechanisms.contains Sasl.Scram.mechanismName
  let offersPlus := mechanisms.contains Sasl.Scram.plusMechanismName
  match mode, tlsServerEndPoint with
  | .require, none => throw .tlsRequired
  | .require, some binding =>
    if offersPlus then
      pure (.tlsServerEndPoint binding)
    else
      throw .plusNotOffered
  | .prefer, none =>
    if offersPlus then
      throw .plusWithoutTls
    else if offersBase then
      pure .none
    else
      throw .plusNotOffered
  | .disable, none =>
    if offersPlus then
      throw .plusWithoutTls
    else if offersBase then
      pure .none
    else
      throw .plusNotOffered
  | .disable, some _ =>
    if offersBase then
      pure .none
    else
      throw .plusNotOffered
  | .prefer, some binding =>
    if offersPlus then
      pure (.tlsServerEndPoint binding)
    else if offersBase then
      pure .supportedNotUsed
    else
      throw .plusNotOffered

private def upsert (params : Array (String × String)) (name value : String) :
    Array (String × String) :=
  match params.findIdx? (·.1 == name) with
  | some i => params.set! i (name, value)
  | none => params.push (name, value)

/-- Initial state plus the StartupMessage bytes. (SSLRequest negotiation, if
any, happens in the shell before this — its unframed 1-byte reply cannot flow
through `step`.) -/
def start (cfg : Config) : State × ByteArray :=
  let params := #[("user", cfg.user)]
    ++ (match cfg.database with
        | some db => #[("database", db)]
        | none => #[])
    ++ cfg.parameters.filter (fun kv =>
        kv.1 != "user" && kv.1 != "database" && kv.1 != "client_encoding")
    ++ #[("client_encoding", "UTF8")]
  let version := match cfg.requestedVersion with
    | .v3_0 => protocolVersion
    | .v3_2 => protocolVersion32
  ({ cfg
     phase := .startup .awaitingRequest
     protocolVersion := cfg.requestedVersion },
   encodeStartup params version)

private def requirePassword (s : State) : Except PgError String :=
  match s.cfg.password with
  | some pw => pure pw
  | none => throw .missingPassword

private def authName : AuthRequest → String
  | .kerberosV5 => "KerberosV5"
  | .gss => "GSS"
  | .gssContinue _ => "GSSContinue"
  | .sspi => "SSPI"
  | .unknown code => s!"auth code {code}"
  | _ => "?"

/-- Result triple: no events, no bytes. -/
private def quiet (s : State) : State × Array Event × ByteArray :=
  (s, #[], ByteArray.empty)

private def stepStartup (s : State) (auth : AuthState) (m : BackendMsg) :
    Except PgError (State × Array Event × ByteArray) := do
  match m with
  | .auth req =>
    if s.cfg.channelBinding == .require && auth matches .awaitingRequest then
      unless req matches .sasl _ do
        throw (.channelBinding .plusNotOffered)
    match req, auth with
    | .ok, .awaitingRequest | .ok, .sentCleartext | .ok, .sentMd5 | .ok, .saslDone =>
      pure ({ s with phase := .startup .awaitingReady }, #[.authOk], ByteArray.empty)
    | .ok, .scram _ =>
      -- AuthenticationOk without a SASLFinal: server signature never arrived
      throw (.authFailed "server skipped its SASL final message (no server signature)")
    | .cleartextPassword, .awaitingRequest =>
      let pw ← requirePassword s
      pure ({ s with phase := .startup .sentCleartext }, #[], Frontend.password pw)
    | .md5Password salt, .awaitingRequest =>
      let pw ← requirePassword s
      pure ({ s with phase := .startup .sentMd5 }, #[],
        Frontend.password (Crypto.md5PasswordHash s.cfg.user pw salt))
    | .sasl mechanisms, .awaitingRequest =>
      let binding ← match selectScramChannelBinding s.cfg.channelBinding
          s.cfg.tlsServerEndPoint mechanisms with
        | .ok binding => pure binding
        | .error failure =>
          if s.cfg.channelBinding == .require ||
              failure == .plusWithoutTls then
            throw (.channelBinding failure)
          else
            throw (.unsupportedAuth (String.intercalate ", " mechanisms.toList))
      let pw ← requirePassword s
      let (client, firstMsg) := Sasl.Scram.clientFirstWithChannelBinding
        binding s.cfg.user pw s.cfg.scramNonce
      pure ({
          s with
          phase := .startup (.scram client)
          negotiatedSaslMechanism := some binding.mechanism
        }, #[], Frontend.saslInitialResponse binding.mechanism firstMsg.toUTF8)
    | .saslContinue data, .scram client =>
      let some serverFirst := String.fromUTF8? data
        | throw (.protocol "SASL server-first is not UTF-8")
      match Sasl.Scram.clientFinal client serverFirst with
      | .ok (client, final) =>
        pure ({ s with phase := .startup (.scram client) }, #[],
          Frontend.saslResponse final.toUTF8)
      | .error e => throw (.authFailed s!"SCRAM: {repr e}")
    | .saslFinal data, .scram client =>
      let some serverFinal := String.fromUTF8? data
        | throw (.protocol "SASL server-final is not UTF-8")
      match Sasl.Scram.verifyServerFinal client serverFinal with
      | .ok () => pure ({ s with phase := .startup .saslDone }, #[], ByteArray.empty)
      | .error e => throw (.authFailed s!"SCRAM: {repr e}")
    | .kerberosV5, _ | .gss, _ | .gssContinue _, _ | .sspi, _ | .unknown _, _ =>
      throw (.unsupportedAuth (authName req))
    | _, _ => throw (.protocol "authentication request out of sequence")
  | .backendKeyData pid secret =>
    unless auth matches .awaitingReady do
      throw (.protocol "BackendKeyData before AuthenticationOk")
    if s.protocolVersion == .v3_0 && secret.size != 4 then
      throw (.protocol s!"protocol 3.0 cancel key must be 4 bytes, got {secret.size}")
    pure (quiet { s with backendKey := some { processId := pid, secret } })
  | .negotiateProtocolVersion newest unrecognized =>
    unless auth matches .awaitingRequest do
      throw (.protocol "NegotiateProtocolVersion after authentication began")
    -- The field carries the newest protocol version the server supports.
    -- PostgreSQL sends the full code (e.g. 196608 = 3.0); the docs' wording
    -- ("newest minor") suggests a bare minor, so accept both encodings.
    let version ← match newest.toNat with
      | 0 | 196608 => pure ProtocolVersion.v3_0
      | 2 | 196610 => pure ProtocolVersion.v3_2
      | v => throw (.protocol s!"server negotiated unsupported protocol version {v}")
    pure ({ s with protocolVersion := version },
      #[.negotiatedVersion version unrecognized], ByteArray.empty)
  | .readyForQuery tx =>
    unless auth matches .awaitingReady do
      throw (.protocol "ReadyForQuery before AuthenticationOk")
    pure ({ s with phase := .running {}, txStatus := tx }, #[.ready tx], ByteArray.empty)
  | .errorResponse fields => throw (.serverFatal fields)
  | other => throw (.protocol s!"unexpected message during startup: {repr other}")

/-- Pop the current op, promoting the next queued kind. -/
private def advance (pipe : Pipeline) : Pipeline :=
  match pipe.queued[0]? with
  | some kind => { pipe with current := some { kind }, queued := pipe.queued.extract 1 pipe.queued.size }
  | none => { pipe with current := none }

private def withPipe (s : State) (pipe : Pipeline) : State :=
  { s with phase := .running pipe }

/-- Terminal reply for the current op: emit and advance. -/
private def finish (s : State) (pipe : Pipeline) (ev : Event) :
    State × Array Event × ByteArray :=
  (withPipe s (advance pipe), #[ev], ByteArray.empty)

/-- Non-terminal reply: emit and set the current op's progress. -/
private def progressTo (s : State) (pipe : Pipeline) (op : CurrentOp) (p : Progress)
    (ev : Event) : State × Array Event × ByteArray :=
  (withPipe s { pipe with current := some { op with progress := p } }, #[ev], ByteArray.empty)

/-- Extended-protocol error recovery: cancel expectations up to the next Sync.
If one is queued it becomes the current (draining) op; otherwise the pipeline
is aborted until the user submits a Sync. -/
private def abortToSync (pipe : Pipeline) : Pipeline :=
  match dropAborted (· == OpKind.sync) pipe.queued with
  | (rest, true) =>
    { pipe with
      current := some { kind := .sync, progress := .drainError }
      queued := rest.extract 1 rest.size }
  | (_, false) => { pipe with current := none, queued := #[], aborted := true }

/-- Ops answered by the simple-query statement cycle vs the extended protocol
— determines which error-recovery path an ErrorResponse takes. -/
private def isSimple (op : CurrentOp) : Bool := op.kind == .simpleQuery

private def stepRunning (s : State) (pipe : Pipeline) (m : BackendMsg) :
    Except PgError (State × Array Event × ByteArray) := do
  match m with
  | .errorResponse fields =>
    match pipe.current with
    | none =>
      if pipe.aborted then
        -- already draining a Flush-caused abort; nothing further to cancel
        pure (s, #[.errorResponse fields], ByteArray.empty)
      else
        -- unsolicited while quiescent: the backend is going down
        throw (.serverFatal fields)
    | some op =>
      if isSimple op then
        pure (progressTo s pipe op .drainError (.errorResponse fields))
      else if op.kind == .sync then
        -- keep draining to this sync's ReadyForQuery
        pure (progressTo s pipe op .drainError (.errorResponse fields))
      else
        pure (withPipe s (abortToSync pipe), #[.errorResponse fields], ByteArray.empty)
  | .readyForQuery tx =>
    match pipe.current with
    | some op =>
      if op.kind == .sync || op.kind == .simpleQuery then
        let (s', evs, out) := finish { s with txStatus := tx } pipe (.ready tx)
        pure (s', evs, out)
      else
        throw (.protocol s!"ReadyForQuery while awaiting replies for {repr op.kind}")
    | none => throw (.protocol "unsolicited ReadyForQuery")
  | .parseComplete =>
    let some op := pipe.current | throw (.protocol "unsolicited ParseComplete")
    unless op.kind == .parse && op.progress == .start do
      throw (.protocol "unexpected ParseComplete")
    pure (finish s pipe .parseComplete)
  | .bindComplete =>
    let some op := pipe.current | throw (.protocol "unsolicited BindComplete")
    unless op.kind == .bind && op.progress == .start do
      throw (.protocol "unexpected BindComplete")
    pure (finish s pipe .bindComplete)
  | .closeComplete =>
    let some op := pipe.current | throw (.protocol "unsolicited CloseComplete")
    unless op.kind == .close && op.progress == .start do
      throw (.protocol "unexpected CloseComplete")
    pure (finish s pipe .closeComplete)
  | .parameterDescription oids =>
    let some op := pipe.current | throw (.protocol "unsolicited ParameterDescription")
    unless op.kind == .describeStatement && op.progress == .start do
      throw (.protocol "unexpected ParameterDescription")
    pure (progressTo s pipe op .descParams (.parameterDescription oids))
  | .rowDescription columns =>
    let some op := pipe.current | throw (.protocol "unsolicited RowDescription")
    match op.kind, op.progress with
    | .describeStatement, .descParams => pure (finish s pipe (.rowDescription columns))
    | .describePortal, .start => pure (finish s pipe (.rowDescription columns))
    | .simpleQuery, .start => pure (progressTo s pipe op (.rows (some columns.size))
        (.rowDescription columns))
    | _, _ => throw (.protocol "unexpected RowDescription")
  | .noData =>
    let some op := pipe.current | throw (.protocol "unsolicited NoData")
    match op.kind, op.progress with
    | .describeStatement, .descParams => pure (finish s pipe .noData)
    | .describePortal, .start => pure (finish s pipe .noData)
    | _, _ => throw (.protocol "unexpected NoData")
  | .dataRow columns =>
    let some op := pipe.current | throw (.protocol "unsolicited DataRow")
    match op.kind, op.progress with
    | .execute, .start => pure (progressTo s pipe op (.rows none) (.dataRow columns))
    | .execute, .rows _ =>
      pure (withPipe s pipe, #[.dataRow columns], ByteArray.empty)
    | .simpleQuery, .rows cols =>
      if let some n := cols then
        unless columns.size == n do
          throw (.protocol s!"DataRow arity {columns.size}, RowDescription said {n}")
      pure (withPipe s pipe, #[.dataRow columns], ByteArray.empty)
    | _, _ => throw (.protocol "DataRow without a RowDescription/Execute context")
  | .commandComplete tag =>
    let some op := pipe.current | throw (.protocol "unsolicited CommandComplete")
    match op.kind with
    | .execute => pure (finish s pipe (.commandComplete tag))
    | .simpleQuery =>
      -- statement finished; more statements may follow until ReadyForQuery
      pure (progressTo s pipe op .start (.commandComplete tag))
    | _ => throw (.protocol "unexpected CommandComplete")
  | .emptyQueryResponse =>
    let some op := pipe.current | throw (.protocol "unsolicited EmptyQueryResponse")
    match op.kind with
    | .execute => pure (finish s pipe .emptyQuery)
    | .simpleQuery => pure (progressTo s pipe op .start .emptyQuery)
    | _ => throw (.protocol "unexpected EmptyQueryResponse")
  | .portalSuspended =>
    let some op := pipe.current | throw (.protocol "unsolicited PortalSuspended")
    unless op.kind == .execute do throw (.protocol "unexpected PortalSuspended")
    pure (finish s pipe .portalSuspended)
  | .copyInResponse overall formats =>
    let some op := pipe.current | throw (.protocol "unsolicited CopyInResponse")
    unless (op.kind == .execute || op.kind == .simpleQuery) && op.progress == .start do
      throw (.protocol "unexpected CopyInResponse")
    -- Frontend messages already pipelined behind this op would be consumed as
    -- COPY data by the backend — unrecoverable (a trailing Sync is harmless).
    unless pipe.queued.all (· == OpKind.sync) && pipe.queued.size ≤ 1 do
      throw (.protocol "COPY started with operations pipelined behind it")
    let info : CopyInfo := { binary := overall == 1, columnFormats := formats }
    pure (progressTo s pipe op (.copyIn info false) (.copyInStarted info))
  | .copyOutResponse overall formats =>
    let some op := pipe.current | throw (.protocol "unsolicited CopyOutResponse")
    unless (op.kind == .execute || op.kind == .simpleQuery) && op.progress == .start do
      throw (.protocol "unexpected CopyOutResponse")
    unless pipe.queued.all (· == OpKind.sync) && pipe.queued.size ≤ 1 do
      throw (.protocol "COPY started with operations pipelined behind it")
    let info : CopyInfo := { binary := overall == 1, columnFormats := formats }
    pure (progressTo s pipe op (.copyOut info) (.copyOutStarted info))
  | .copyData data =>
    let some op := pipe.current | throw (.protocol "unsolicited CopyData")
    match op.progress with
    | .copyOut _ => pure (withPipe s pipe, #[.copyData data], ByteArray.empty)
    | _ => throw (.protocol "CopyData outside COPY OUT")
  | .copyDone =>
    let some op := pipe.current | throw (.protocol "unsolicited CopyDone")
    match op.progress with
    | .copyOut _ => pure (progressTo s pipe op .start .copyOutDone)
    | _ => throw (.protocol "CopyDone outside COPY OUT")
  | .copyBothResponse .. => throw (.protocol "CopyBothResponse (replication) not supported")
  | .functionCallResponse _ => throw (.protocol "FunctionCallResponse not supported")
  | .auth _ => throw (.protocol "authentication request after startup")
  | .backendKeyData .. => throw (.protocol "BackendKeyData after startup")
  | .negotiateProtocolVersion .. => throw (.protocol "NegotiateProtocolVersion after startup")
  | .noticeResponse _ | .parameterStatus .. | .notificationResponse .. =>
    -- unreachable: handled by the async pre-filter in `step`
    throw (.protocol "async message reached phase dispatch")

/-- Advance on one framed backend message. On `.ok (s', events, out)`: events
in wire order, `out` = protocol-driven bytes to write (auth responses; empty
after startup). On `.error`: the connection is poisoned — close the socket. -/
def step (s : State) (msg : RawMessage) : Except PgError (State × Array Event × ByteArray) := do
  if s.phase matches .closed then
    throw (.protocol "message received after Terminate")
  let m ← match Backend.decode msg with
    | .ok m => pure m
    | .error e => throw (.decode e)
  -- async messages are valid in every phase
  match m with
  | .noticeResponse fields => pure (s, #[.notice fields], ByteArray.empty)
  | .parameterStatus name value =>
    pure ({ s with params := upsert s.params name value },
      #[.parameterStatus name value], ByteArray.empty)
  | .notificationResponse pid channel payload =>
    pure (s, #[.notification pid channel payload], ByteArray.empty)
  | _ =>
    match s.phase with
    | .startup auth => stepStartup s auth m
    | .running pipe => stepRunning s pipe m
    | .closed => throw (.protocol "unreachable")

/-- `step` each frame in order, accumulating events and output bytes. -/
private def runSteps (s : State) (msgs : List RawMessage) (events : Array Event)
    (out : ByteArray) : Except PgError (State × Array Event × ByteArray) :=
  match msgs with
  | [] => pure (s, events, out)
  | m :: rest => do
    let (s', evs, bytes) ← step s m
    runSteps s' rest (events ++ evs) (out ++ bytes)

/-- Shell entry point: buffer a TCP chunk, then `step` each completed frame.
Feeding byte-at-a-time is semantically identical to feeding whole — the
fragmentation-torture hook. -/
def feed (s : State) (chunk : ByteArray) : Except PgError (State × Array Event × ByteArray) := do
  let fed ← match s.decode.feed chunk with
    | .ok st => pure st
    | .error e => throw (.decode e)
  let (msgs, decode) := fed.take
  runSteps { s with decode } msgs.toList #[] ByteArray.empty

/-- Queue an op behind the pipeline. -/
private def enqueue (pipe : Pipeline) (kind : OpKind) : Pipeline :=
  match pipe.current with
  | none => { pipe with current := some { kind } }
  | some _ => { pipe with queued := pipe.queued.push kind }

/-- Post-COPY-gate submission: the pipeline is not receiving COPY IN data. -/
private def submitIdle (s : State) (pipe : Pipeline) (req : Request) :
    Except PgError (State × ByteArray) :=
  if pipe.aborted then
    match req with
    | .sync =>
      let pipe := enqueue { pipe with aborted := false } .sync
      pure (withPipe s pipe, Frontend.sync)
    | .terminate => pure ({ s with phase := .closed }, encodeTerminate)
    | _ => throw .rejectedAborted
  else
    match req with
    | .simpleQuery sql => pure (withPipe s (enqueue pipe .simpleQuery), encodeQuery sql)
    | .parse name sql oids => pure (withPipe s (enqueue pipe .parse), Frontend.parse name sql oids)
    | .bind portal stmt pf ps rf =>
      pure (withPipe s (enqueue pipe .bind), Frontend.bind portal stmt pf ps rf)
    | .describeStatement name =>
      pure (withPipe s (enqueue pipe .describeStatement), Frontend.describeStatement name)
    | .describePortal name =>
      pure (withPipe s (enqueue pipe .describePortal), Frontend.describePortal name)
    | .execute portal maxRows =>
      pure (withPipe s (enqueue pipe .execute), Frontend.execute portal maxRows)
    | .closeStatement name =>
      pure (withPipe s (enqueue pipe .close), Frontend.closeStatement name)
    | .closePortal name =>
      pure (withPipe s (enqueue pipe .close), Frontend.closePortal name)
    | .flush => pure (s, Frontend.flush)
    | .sync => pure (withPipe s (enqueue pipe .sync), Frontend.sync)
    | .copyData _ | .copyDone | .copyFail _ =>
      throw (.rejectedInvalid "no COPY IN in progress")
    | .terminate => pure ({ s with phase := .closed }, encodeTerminate)

private def submitRunning (s : State) (pipe : Pipeline) (req : Request) :
    Except PgError (State × ByteArray) :=
  -- COPY IN reverses the data direction: only copy traffic may flow
  match pipe.current with
  | some op =>
    match op.progress with
    | .copyIn info false =>
      match req with
      | .copyData data => pure (s, Frontend.copyData data)
      | .copyDone =>
        let pipe := { pipe with current := some { op with progress := .copyIn info true } }
        pure (withPipe s pipe, Frontend.copyDone)
      | .copyFail reason =>
        let pipe := { pipe with current := some { op with progress := .copyIn info true } }
        pure (withPipe s pipe, Frontend.copyFail reason)
      | .flush => pure (s, Frontend.flush)
      | .terminate => pure ({ s with phase := .closed }, encodeTerminate)
      | _ => throw (.rejectedInvalid "COPY IN in progress")
    | _ => submitIdle s pipe req
  | none => submitIdle s pipe req

/-- User-initiated action. Failure is a rejection: state unchanged, connection
healthy. Success returns bytes to write. -/
def submit (s : State) (req : Request) : Except PgError (State × ByteArray) := do
  match s.phase with
  | .closed => throw (.rejectedInvalid "connection closed")
  | .startup _ =>
    match req with
    | .terminate => pure ({ s with phase := .closed }, encodeTerminate)
    | _ => throw (.rejectedInvalid "connection still starting up")
  | .running pipe => submitRunning s pipe req

def submitAll (s : State) (reqs : Array Request) : Except PgError (State × ByteArray) := do
  let mut cur := s
  let mut out := ByteArray.empty
  for req in reqs do
    let (s', bytes) ← submit cur req
    cur := s'
    out := out ++ bytes
  pure (cur, out)

/-!
### Machine invariant

`State.WellFormed` captures the structural coherence the shell relies on:

- **Phase coherence**: during startup the transaction status is still `idle`,
  and once SCRAM has started a negotiated mechanism is recorded.
- **Pending-queue coherence**: replies are only ever expected for the op at
  the head of the pipeline (`current = none → queued = #[]`), and the head
  op's reply progress matches its kind (a `descParams` head is a
  describeStatement, a counted `rows` head is a simple query, ...).
- **Error-drain/Sync-boundary coherence**: an aborted pipeline is fully
  drained (`aborted → current = none ∧ queued = #[]`), and a `drainError`
  head is exactly a Sync (extended protocol) or simple query — the two ops
  whose ReadyForQuery ends recovery.
- **COPY coherence**: while COPY IN is receiving data (`copyIn _ false`)
  nothing beyond at most one trailing Sync is pipelined behind it.

`submit` and `step` preserve it (`submit_wellFormed`, `step_wellFormed`,
`feed_wellFormed`); a rejected submission returns no state at all and only
rejection errors (`submit_error_rejection`), and async messages never touch
the pipeline (`step_async_preserves_pipeline`).
-/

/-- The head op's reply progress is possible for its kind. -/
def CurrentOp.Coherent (op : CurrentOp) : Prop :=
  match op.progress with
  | .start => True
  | .descParams => op.kind = .describeStatement
  | .rows (some _) => op.kind = .simpleQuery
  | .rows none => op.kind = .execute
  | .copyIn _ _ => op.kind = .execute ∨ op.kind = .simpleQuery
  | .copyOut _ => op.kind = .execute ∨ op.kind = .simpleQuery
  | .drainError => op.kind = .sync ∨ op.kind = .simpleQuery

def Pipeline.WellFormed (pipe : Pipeline) : Prop :=
  (pipe.aborted = true → pipe.current = none ∧ pipe.queued = #[]) ∧
  (pipe.current = none → pipe.queued = #[]) ∧
  (match pipe.current with
   | none => True
   | some op =>
     op.Coherent ∧
     (match op.progress with
      | .copyIn _ false =>
        pipe.queued.all (· == OpKind.sync) = true ∧ pipe.queued.size ≤ 1
      | _ => True))

def State.WellFormed (s : State) : Prop :=
  match s.phase with
  | .startup auth =>
    s.txStatus = .idle ∧
    (match auth with
     | .scram _ => s.negotiatedSaslMechanism.isSome = true
     | _ => True)
  | .running pipe => pipe.WellFormed
  | .closed => True

theorem start_wellFormed (cfg : Config) : (start cfg).1.WellFormed := by
  unfold start State.WellFormed
  exact ⟨rfl, True.intro⟩

private theorem emptyPipeline_wf : (({} : Pipeline)).WellFormed := by
  unfold Pipeline.WellFormed
  dsimp only
  exact ⟨(fun h => nomatch h), (fun _ => rfl), True.intro⟩

private theorem advance_wf {pipe : Pipeline} (hab : pipe.aborted = false) :
    (advance pipe).WellFormed := by
  unfold advance
  split
  · unfold Pipeline.WellFormed
    dsimp only
    exact ⟨(fun h => absurd h (by simp [hab])), (fun h => nomatch h), True.intro, True.intro⟩
  · next hq =>
    have hqe : pipe.queued = #[] := by
      have hle := Array.getElem?_eq_none_iff.mp hq
      exact Array.eq_empty_of_size_eq_zero (by omega)
    unfold Pipeline.WellFormed
    dsimp only
    exact ⟨(fun _ => ⟨rfl, hqe⟩), (fun _ => hqe), True.intro⟩

private theorem abortToSync_wf {pipe : Pipeline} (hab : pipe.aborted = false) :
    (abortToSync pipe).WellFormed := by
  unfold abortToSync
  split
  · unfold Pipeline.WellFormed
    dsimp only
    exact ⟨(fun h => absurd h (by simp [hab])), (fun h => nomatch h),
      Or.inl rfl, True.intro⟩
  · unfold Pipeline.WellFormed
    dsimp only
    exact ⟨(fun _ => ⟨rfl, rfl⟩), (fun _ => rfl), True.intro⟩

private theorem enqueue_wf {pipe : Pipeline} (hwf : pipe.WellFormed)
    (hab : pipe.aborted = false)
    (hnocopy : ∀ op info, pipe.current = some op → op.progress ≠ .copyIn info false)
    (kind : OpKind) : (enqueue pipe kind).WellFormed := by
  obtain ⟨h1, h2, h3⟩ := hwf
  unfold enqueue
  split
  · next hc =>
    unfold Pipeline.WellFormed
    dsimp only
    exact ⟨(fun h => absurd h (by simp [hab])), (fun h => nomatch h), True.intro, True.intro⟩
  · next op hc =>
    rw [hc] at h3
    unfold Pipeline.WellFormed
    dsimp only
    refine ⟨(fun h => absurd h (by simp [hab])),
      (fun h => absurd h (by simp [hc])), ?_⟩
    simp only [hc]
    refine ⟨h3.1, ?_⟩
    cases hp : op.progress with
    | copyIn info done =>
      cases done with
      | false => exact absurd hp (hnocopy op info hc)
      | true => exact True.intro
    | _ => exact True.intro

private theorem wf_of_phase_running {s : State} {pipe : Pipeline}
    (hphase : s.phase = .running pipe) (hwf : pipe.WellFormed) : s.WellFormed := by
  unfold State.WellFormed
  rw [hphase]
  exact hwf

private theorem pipe_wf_of_running {s : State} {pipe : Pipeline}
    (hphase : s.phase = .running pipe) (hwf : s.WellFormed) : pipe.WellFormed := by
  unfold State.WellFormed at hwf
  rw [hphase] at hwf
  exact hwf

private theorem submitIdle_wf {s : State} {pipe : Pipeline} {req : Request}
    (hphase : s.phase = .running pipe) (hwf : pipe.WellFormed)
    (hnocopy : ∀ op info, pipe.current = some op → op.progress ≠ .copyIn info false) :
    ∀ {s' : State} {out : ByteArray}, submitIdle s pipe req = .ok (s', out) →
      s'.WellFormed := by
  obtain ⟨h1, h2, h3⟩ := hwf
  fun_cases submitIdle s pipe req with
  | case1 habt =>
    intro s' out h
    cases h
    obtain ⟨hc, hq⟩ := h1 habt
    have hwf' : Pipeline.WellFormed { pipe with aborted := false } := by
      refine ⟨(fun hh => nomatch hh), (fun _ => hq), ?_⟩
      show (match pipe.current with
        | none => True
        | some op => op.Coherent ∧ _)
      rw [hc]
      exact True.intro
    show Pipeline.WellFormed (enqueue { pipe with aborted := false } .sync)
    exact enqueue_wf hwf' rfl (fun op info hcur => absurd hcur (by simp [hc])) _
  | case2 habt =>
    intro s' out h
    cases h
    exact True.intro
  | case3 habt hne =>
    intro s' out h
    cases h
  | case4 hnab sql =>
    intro s' out h
    cases h
    show Pipeline.WellFormed (enqueue _ _)
    exact enqueue_wf ⟨h1, h2, h3⟩ (by simpa using hnab) hnocopy _
  | case5 hnab name sql oids =>
    intro s' out h
    cases h
    show Pipeline.WellFormed (enqueue _ _)
    exact enqueue_wf ⟨h1, h2, h3⟩ (by simpa using hnab) hnocopy _
  | case6 hnab portal stmt pf ps rf =>
    intro s' out h
    cases h
    show Pipeline.WellFormed (enqueue _ _)
    exact enqueue_wf ⟨h1, h2, h3⟩ (by simpa using hnab) hnocopy _
  | case7 hnab name =>
    intro s' out h
    cases h
    show Pipeline.WellFormed (enqueue _ _)
    exact enqueue_wf ⟨h1, h2, h3⟩ (by simpa using hnab) hnocopy _
  | case8 hnab name =>
    intro s' out h
    cases h
    show Pipeline.WellFormed (enqueue _ _)
    exact enqueue_wf ⟨h1, h2, h3⟩ (by simpa using hnab) hnocopy _
  | case9 hnab portal maxRows =>
    intro s' out h
    cases h
    show Pipeline.WellFormed (enqueue _ _)
    exact enqueue_wf ⟨h1, h2, h3⟩ (by simpa using hnab) hnocopy _
  | case10 hnab name =>
    intro s' out h
    cases h
    show Pipeline.WellFormed (enqueue _ _)
    exact enqueue_wf ⟨h1, h2, h3⟩ (by simpa using hnab) hnocopy _
  | case11 hnab name =>
    intro s' out h
    cases h
    show Pipeline.WellFormed (enqueue _ _)
    exact enqueue_wf ⟨h1, h2, h3⟩ (by simpa using hnab) hnocopy _
  | case12 hnab =>
    intro s' out h
    cases h
    exact wf_of_phase_running hphase ⟨h1, h2, h3⟩
  | case13 hnab =>
    intro s' out h
    cases h
    show Pipeline.WellFormed (enqueue _ _)
    exact enqueue_wf ⟨h1, h2, h3⟩ (by simpa using hnab) hnocopy _
  | case14 hnab data =>
    intro s' out h
    cases h
  | case15 hnab =>
    intro s' out h
    cases h
  | case16 hnab reason =>
    intro s' out h
    cases h
  | case17 hnab =>
    intro s' out h
    cases h
    exact True.intro

private theorem submitRunning_wf {s : State} {pipe : Pipeline} {req : Request}
    (hphase : s.phase = .running pipe) (hwf : pipe.WellFormed) :
    ∀ {s' : State} {out : ByteArray}, submitRunning s pipe req = .ok (s', out) →
      s'.WellFormed := by
  fun_cases submitRunning s pipe req with
  | case1 op hcur info hprog data =>
    intro s' out h
    cases h
    exact wf_of_phase_running hphase hwf
  | case2 op hcur info hprog =>
    intro s' out h
    cases h
    obtain ⟨h1, h2, h3⟩ := hwf
    show Pipeline.WellFormed _
    refine ⟨(fun habt => absurd (h1 habt).1 (by simp [hcur])), (fun hh => nomatch hh),
      ?_, True.intro⟩
    rw [hcur] at h3
    have hcoh := h3.1
    unfold CurrentOp.Coherent at hcoh ⊢
    rw [hprog] at hcoh
    exact hcoh
  | case3 op hcur info hprog reason =>
    intro s' out h
    cases h
    obtain ⟨h1, h2, h3⟩ := hwf
    show Pipeline.WellFormed _
    refine ⟨(fun habt => absurd (h1 habt).1 (by simp [hcur])), (fun hh => nomatch hh),
      ?_, True.intro⟩
    rw [hcur] at h3
    have hcoh := h3.1
    unfold CurrentOp.Coherent at hcoh ⊢
    rw [hprog] at hcoh
    exact hcoh
  | case4 op hcur info hprog =>
    intro s' out h
    cases h
    exact wf_of_phase_running hphase hwf
  | case5 op hcur info hprog =>
    intro s' out h
    cases h
    exact True.intro
  | case6 op hcur info hprog hne =>
    intro s' out h
    cases h
  | case7 =>
    rename_i op hcur hnot
    intro s' out h
    refine submitIdle_wf hphase hwf ?_ h
    intro op' info hcur'
    rw [hcur] at hcur'
    injection hcur' with heq
    subst heq
    intro hp
    exact hnot info hp
  | case8 =>
    rename_i hcur
    intro s' out h
    refine submitIdle_wf hphase hwf ?_ h
    intro op' info hcur'
    rw [hcur] at hcur'
    cases hcur'

/-- `submit` preserves well-formedness. -/
theorem submit_wellFormed {s : State} {req : Request} {s' : State} {out : ByteArray}
    (hwf : s.WellFormed) (h : submit s req = .ok (s', out)) : s'.WellFormed := by
  revert h
  fun_cases submit s req
  case case2 =>
    intro h
    cases h
    exact True.intro
  case case4 =>
    rename_i pipe hph
    intro h
    exact submitRunning_wf hph (pipe_wf_of_running hph hwf) h
  all_goals intro h
  all_goals cases h

/-- A failed `submit` is a *rejection*: no new state exists at all (so the
machine is trivially unchanged), and the error is always `rejectedInvalid`
or `rejectedAborted` — never a connection-poisoning class. -/
theorem submit_error_rejection {s : State} {req : Request} {e : PgError}
    (h : submit s req = .error e) :
    e = .rejectedAborted ∨ ∃ why, e = .rejectedInvalid why := by
  have idle : ∀ (s₀ : State) (pipe : Pipeline) (req₀ : Request),
      submitIdle s₀ pipe req₀ = .error e →
      e = .rejectedAborted ∨ ∃ why, e = .rejectedInvalid why := by
    intro s₀ pipe req₀
    fun_cases submitIdle s₀ pipe req₀ <;> intro h' <;> cases h' <;>
      first
        | exact Or.inl rfl
        | exact Or.inr ⟨_, rfl⟩
  have running : ∀ (s₀ : State) (pipe : Pipeline) (req₀ : Request),
      submitRunning s₀ pipe req₀ = .error e →
      e = .rejectedAborted ∨ ∃ why, e = .rejectedInvalid why := by
    intro s₀ pipe req₀
    fun_cases submitRunning s₀ pipe req₀ <;> intro h' <;>
      first
        | exact idle _ _ _ h'
        | (cases h' <;> first
            | exact Or.inl rfl
            | exact Or.inr ⟨_, rfl⟩)
  revert h
  fun_cases submit s req <;> intro h <;>
    first
      | exact running _ _ _ h
      | (cases h <;> first
          | exact Or.inl rfl
          | exact Or.inr ⟨_, rfl⟩)

end Machine
end Protocol
end Pg
