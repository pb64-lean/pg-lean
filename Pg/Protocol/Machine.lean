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
error-recovery drop rule the machine applies internally. That FIFO rule is
`shellStep`, and it is *proved* to track the machine's own pending-op queue
(`Pipeline.pending`) on every accepted message and submission — see the
trace-level FIFO attribution section.
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
    Except PgError (State × Array Event × ByteArray) :=
  match m with
  | .auth req =>
    if s.cfg.channelBinding == .require && (auth matches .awaitingRequest) &&
        !(req matches .sasl _) then
      throw (.channelBinding .plusNotOffered)
    else
      match req, auth with
      | .ok, .awaitingRequest | .ok, .sentCleartext | .ok, .sentMd5 | .ok, .saslDone =>
        pure ({ s with phase := .startup .awaitingReady }, #[.authOk], ByteArray.empty)
      | .ok, .scram _ =>
        -- AuthenticationOk without a SASLFinal: server signature never arrived
        throw (.authFailed "server skipped its SASL final message (no server signature)")
      | .cleartextPassword, .awaitingRequest =>
        match requirePassword s with
        | .error e => throw e
        | .ok pw =>
          pure ({ s with phase := .startup .sentCleartext }, #[], Frontend.password pw)
      | .md5Password salt, .awaitingRequest =>
        match requirePassword s with
        | .error e => throw e
        | .ok pw =>
          pure ({ s with phase := .startup .sentMd5 }, #[],
            Frontend.password (Crypto.md5PasswordHash s.cfg.user pw salt))
      | .sasl mechanisms, .awaitingRequest =>
        match selectScramChannelBinding s.cfg.channelBinding
            s.cfg.tlsServerEndPoint mechanisms with
        | .error failure =>
          if s.cfg.channelBinding == .require ||
              failure == .plusWithoutTls then
            throw (.channelBinding failure)
          else
            throw (.unsupportedAuth (String.intercalate ", " mechanisms.toList))
        | .ok binding =>
          match requirePassword s with
          | .error e => throw e
          | .ok pw =>
            let (client, firstMsg) := Sasl.Scram.clientFirstWithChannelBinding
              binding s.cfg.user pw s.cfg.scramNonce
            pure ({
                s with
                phase := .startup (.scram client)
                negotiatedSaslMechanism := some binding.mechanism
              }, #[], Frontend.saslInitialResponse binding.mechanism firstMsg.toUTF8)
      | .saslContinue data, .scram client =>
        match String.fromUTF8? data with
        | none => throw (.protocol "SASL server-first is not UTF-8")
        | some serverFirst =>
          match Sasl.Scram.clientFinal client serverFirst with
          | .ok (client, final) =>
            pure ({ s with phase := .startup (.scram client) }, #[],
              Frontend.saslResponse final.toUTF8)
          | .error e => throw (.authFailed s!"SCRAM: {repr e}")
      | .saslFinal data, .scram client =>
        match String.fromUTF8? data with
        | none => throw (.protocol "SASL server-final is not UTF-8")
        | some serverFinal =>
          match Sasl.Scram.verifyServerFinal client serverFinal with
          | .ok () => pure ({ s with phase := .startup .saslDone }, #[], ByteArray.empty)
          | .error e => throw (.authFailed s!"SCRAM: {repr e}")
      | .kerberosV5, _ | .gss, _ | .gssContinue _, _ | .sspi, _ | .unknown _, _ =>
        throw (.unsupportedAuth (authName req))
      | _, _ => throw (.protocol "authentication request out of sequence")
  | .backendKeyData pid secret =>
    if auth matches .awaitingReady then
      if s.protocolVersion == .v3_0 && secret.size != 4 then
        throw (.protocol s!"protocol 3.0 cancel key must be 4 bytes, got {secret.size}")
      else
        pure (quiet { s with backendKey := some { processId := pid, secret } })
    else
      throw (.protocol "BackendKeyData before AuthenticationOk")
  | .negotiateProtocolVersion newest unrecognized =>
    if auth matches .awaitingRequest then
      -- The field carries the newest protocol version the server supports.
      -- PostgreSQL sends the full code (e.g. 196608 = 3.0); the docs' wording
      -- ("newest minor") suggests a bare minor, so accept both encodings.
      match newest.toNat with
      | 0 | 196608 =>
        pure ({ s with protocolVersion := ProtocolVersion.v3_0 },
          #[.negotiatedVersion .v3_0 unrecognized], ByteArray.empty)
      | 2 | 196610 =>
        pure ({ s with protocolVersion := ProtocolVersion.v3_2 },
          #[.negotiatedVersion .v3_2 unrecognized], ByteArray.empty)
      | v => throw (.protocol s!"server negotiated unsupported protocol version {v}")
    else
      throw (.protocol "NegotiateProtocolVersion after authentication began")
  | .readyForQuery tx =>
    if auth matches .awaitingReady then
      pure ({ s with phase := .running {}, txStatus := tx }, #[.ready tx], ByteArray.empty)
    else
      throw (.protocol "ReadyForQuery before AuthenticationOk")
  | .errorResponse fields => throw (.serverFatal fields)
  | other => throw (.protocol s!"unexpected message during startup: {repr other}")

/-- Pop the current op, promoting the next queued kind. Public so the
recovery/alignment theorems can characterize the post-`ReadyForQuery` state. -/
def advance (pipe : Pipeline) : Pipeline :=
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
is aborted until the user submits a Sync. Public so the error-recovery
theorems can characterize the post-error state. -/
def abortToSync (pipe : Pipeline) : Pipeline :=
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
    Except PgError (State × Array Event × ByteArray) :=
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
        pure (finish { s with txStatus := tx } pipe (.ready tx))
      else
        throw (.protocol s!"ReadyForQuery while awaiting replies for {repr op.kind}")
    | none => throw (.protocol "unsolicited ReadyForQuery")
  | .parseComplete =>
    match pipe.current with
    | none => throw (.protocol "unsolicited ParseComplete")
    | some op =>
      if op.kind == .parse && op.progress == .start then
        pure (finish s pipe .parseComplete)
      else
        throw (.protocol "unexpected ParseComplete")
  | .bindComplete =>
    match pipe.current with
    | none => throw (.protocol "unsolicited BindComplete")
    | some op =>
      if op.kind == .bind && op.progress == .start then
        pure (finish s pipe .bindComplete)
      else
        throw (.protocol "unexpected BindComplete")
  | .closeComplete =>
    match pipe.current with
    | none => throw (.protocol "unsolicited CloseComplete")
    | some op =>
      if op.kind == .close && op.progress == .start then
        pure (finish s pipe .closeComplete)
      else
        throw (.protocol "unexpected CloseComplete")
  | .parameterDescription oids =>
    match pipe.current with
    | none => throw (.protocol "unsolicited ParameterDescription")
    | some op =>
      if op.kind == .describeStatement && op.progress == .start then
        pure (progressTo s pipe op .descParams (.parameterDescription oids))
      else
        throw (.protocol "unexpected ParameterDescription")
  | .rowDescription columns =>
    match pipe.current with
    | none => throw (.protocol "unsolicited RowDescription")
    | some op =>
      match op.kind, op.progress with
      | .describeStatement, .descParams => pure (finish s pipe (.rowDescription columns))
      | .describePortal, .start => pure (finish s pipe (.rowDescription columns))
      | .simpleQuery, .start => pure (progressTo s pipe op (.rows (some columns.size))
          (.rowDescription columns))
      | _, _ => throw (.protocol "unexpected RowDescription")
  | .noData =>
    match pipe.current with
    | none => throw (.protocol "unsolicited NoData")
    | some op =>
      match op.kind, op.progress with
      | .describeStatement, .descParams => pure (finish s pipe .noData)
      | .describePortal, .start => pure (finish s pipe .noData)
      | _, _ => throw (.protocol "unexpected NoData")
  | .dataRow columns =>
    match pipe.current with
    | none => throw (.protocol "unsolicited DataRow")
    | some op =>
      match op.kind, op.progress with
      | .execute, .start => pure (progressTo s pipe op (.rows none) (.dataRow columns))
      | .execute, .rows _ =>
        pure (withPipe s pipe, #[.dataRow columns], ByteArray.empty)
      | .simpleQuery, .rows cols =>
        match cols with
        | some n =>
          if columns.size == n then
            pure (withPipe s pipe, #[.dataRow columns], ByteArray.empty)
          else
            throw (.protocol s!"DataRow arity {columns.size}, RowDescription said {n}")
        | none => pure (withPipe s pipe, #[.dataRow columns], ByteArray.empty)
      | _, _ => throw (.protocol "DataRow without a RowDescription/Execute context")
  | .commandComplete tag =>
    match pipe.current with
    | none => throw (.protocol "unsolicited CommandComplete")
    | some op =>
      match op.kind with
      | .execute => pure (finish s pipe (.commandComplete tag))
      | .simpleQuery =>
        -- statement finished; more statements may follow until ReadyForQuery
        pure (progressTo s pipe op .start (.commandComplete tag))
      | _ => throw (.protocol "unexpected CommandComplete")
  | .emptyQueryResponse =>
    match pipe.current with
    | none => throw (.protocol "unsolicited EmptyQueryResponse")
    | some op =>
      match op.kind with
      | .execute => pure (finish s pipe .emptyQuery)
      | .simpleQuery => pure (progressTo s pipe op .start .emptyQuery)
      | _ => throw (.protocol "unexpected EmptyQueryResponse")
  | .portalSuspended =>
    match pipe.current with
    | none => throw (.protocol "unsolicited PortalSuspended")
    | some op =>
      if op.kind == .execute then
        pure (finish s pipe .portalSuspended)
      else
        throw (.protocol "unexpected PortalSuspended")
  | .copyInResponse overall formats =>
    match pipe.current with
    | none => throw (.protocol "unsolicited CopyInResponse")
    | some op =>
      if (op.kind == .execute || op.kind == .simpleQuery) && op.progress == .start then
        -- Frontend messages already pipelined behind this op would be consumed
        -- as COPY data by the backend — unrecoverable (a trailing Sync is
        -- harmless).
        if pipe.queued.all (· == OpKind.sync) && pipe.queued.size ≤ 1 then
          let info : CopyInfo := { binary := overall == 1, columnFormats := formats }
          pure (progressTo s pipe op (.copyIn info false) (.copyInStarted info))
        else
          throw (.protocol "COPY started with operations pipelined behind it")
      else
        throw (.protocol "unexpected CopyInResponse")
  | .copyOutResponse overall formats =>
    match pipe.current with
    | none => throw (.protocol "unsolicited CopyOutResponse")
    | some op =>
      if (op.kind == .execute || op.kind == .simpleQuery) && op.progress == .start then
        if pipe.queued.all (· == OpKind.sync) && pipe.queued.size ≤ 1 then
          let info : CopyInfo := { binary := overall == 1, columnFormats := formats }
          pure (progressTo s pipe op (.copyOut info) (.copyOutStarted info))
        else
          throw (.protocol "COPY started with operations pipelined behind it")
      else
        throw (.protocol "unexpected CopyOutResponse")
  | .copyData data =>
    match pipe.current with
    | none => throw (.protocol "unsolicited CopyData")
    | some op =>
      match op.progress with
      | .copyOut _ => pure (withPipe s pipe, #[.copyData data], ByteArray.empty)
      | _ => throw (.protocol "CopyData outside COPY OUT")
  | .copyDone =>
    match pipe.current with
    | none => throw (.protocol "unsolicited CopyDone")
    | some op =>
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
def step (s : State) (msg : RawMessage) : Except PgError (State × Array Event × ByteArray) :=
  if s.phase matches .closed then
    throw (.protocol "message received after Terminate")
  else
    match Backend.decode msg with
    | .error e => throw (.decode e)
    | .ok m =>
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

/-- `step` each frame in order, accumulating events and output bytes. Public
because the framing-bridge theorems (`feed_frames`) factor `feed` through it. -/
def runSteps (s : State) (msgs : List RawMessage) (events : Array Event)
    (out : ByteArray) : Except PgError (State × Array Event × ByteArray) :=
  match msgs with
  | [] => pure (s, events, out)
  | m :: rest =>
    match step s m with
    | .error e => .error e
    | .ok (s', evs, bytes) => runSteps s' rest (events ++ evs) (out ++ bytes)

/-- Shell entry point: buffer a TCP chunk, then `step` each completed frame.
Feeding byte-at-a-time is semantically identical to feeding whole — the
fragmentation-torture hook. -/
def feed (s : State) (chunk : ByteArray) : Except PgError (State × Array Event × ByteArray) :=
  match s.decode.feed chunk with
  | .error e => throw (.decode e)
  | .ok fed =>
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

/-- `submit` each request in order, accumulating output bytes. -/
private def submitList (s : State) (reqs : List Request) (out : ByteArray) :
    Except PgError (State × ByteArray) :=
  match reqs with
  | [] => pure (s, out)
  | req :: rest =>
    match submit s req with
    | .error e => .error e
    | .ok (s', bytes) => submitList s' rest (out ++ bytes)

def submitAll (s : State) (reqs : Array Request) : Except PgError (State × ByteArray) :=
  submitList s reqs.toList ByteArray.empty

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

private theorem submitList_wf :
    ∀ {reqs : List Request} {s : State} {out : ByteArray} {r : State × ByteArray},
      s.WellFormed → submitList s reqs out = .ok r → r.1.WellFormed := by
  intro reqs
  induction reqs with
  | nil =>
    intro s out r hwf h
    cases h
    exact hwf
  | cons req rest ih =>
    intro s out r hwf h
    unfold submitList at h
    cases hsub : submit s req with
    | error e =>
      rw [hsub] at h
      cases h
    | ok res =>
      obtain ⟨s1, b1⟩ := res
      rw [hsub] at h
      exact ih (submit_wellFormed hwf hsub) h

/-- `submitAll` preserves well-formedness across a whole batch of requests. -/
theorem submitAll_wellFormed {s : State} {reqs : Array Request} {s' : State}
    {out : ByteArray} (hwf : s.WellFormed) (h : submitAll s reqs = .ok (s', out)) :
    s'.WellFormed := by
  unfold submitAll at h
  exact submitList_wf hwf h

/-- A failed `submitAll` is the rejection of the first offending request:
always `rejectedInvalid`/`rejectedAborted`, never a poisoning error class. -/
theorem submitAll_error_rejection {s : State} {reqs : Array Request} {e : PgError}
    (h : submitAll s reqs = .error e) :
    e = .rejectedAborted ∨ ∃ why, e = .rejectedInvalid why := by
  unfold submitAll at h
  revert h
  have go : ∀ {l : List Request} {s₀ : State} {out : ByteArray},
      submitList s₀ l out = .error e →
      e = .rejectedAborted ∨ ∃ why, e = .rejectedInvalid why := by
    intro l
    induction l with
    | nil =>
      intro s₀ out h
      cases h
    | cons req rest ih =>
      intro s₀ out h
      unfold submitList at h
      cases hsub : submit s₀ req with
      | error e' =>
        rw [hsub] at h
        cases h
        exact submit_error_rejection hsub
      | ok res =>
        obtain ⟨s1, b1⟩ := res
        rw [hsub] at h
        exact ih h
  exact go

private theorem aborted_false_of_current {pipe : Pipeline} (hwf : pipe.WellFormed)
    {op : CurrentOp} (hcur : pipe.current = some op) : pipe.aborted = false := by
  cases hab : pipe.aborted
  · rfl
  · exact absurd (hwf.1 hab).1 (by simp [hcur])

/-- Queue restriction the invariant demands while a fresh COPY IN is open. -/
private def CopyGate (pipe : Pipeline) (p : Progress) : Prop :=
  match p with
  | .copyIn _ false =>
    pipe.queued.all (· == OpKind.sync) = true ∧ pipe.queued.size ≤ 1
  | _ => True

/-- The updated head op stays coherent, so replacing its progress keeps the
pipeline well-formed. -/
private theorem progressTo_wf {pipe : Pipeline} (hwf : pipe.WellFormed)
    {op : CurrentOp} (hcur : pipe.current = some op) {p : Progress}
    (hcoh : CurrentOp.Coherent { op with progress := p })
    (hgate : CopyGate pipe p) :
    ({ pipe with current := some { op with progress := p } } : Pipeline).WellFormed := by
  refine ⟨(fun habt => absurd (hwf.1 habt).1 (by simp [hcur])), (fun hh => nomatch hh), ?_⟩
  exact ⟨hcoh, hgate⟩

private theorem opKind_eq_of_beq {a b : OpKind} (h : (a == b) = true) : a = b := by
  cases a <;> cases b <;> first | rfl | exact absurd h (by decide)

private theorem stepRunning_wf {s : State} {pipe : Pipeline} {m : BackendMsg}
    (hphase : s.phase = .running pipe) (hwf : pipe.WellFormed) :
    ∀ {s' : State} {evs : Array Event} {out : ByteArray},
      stepRunning s pipe m = .ok (s', evs, out) → s'.WellFormed := by
  fun_cases stepRunning s pipe m <;> intro s' evs out h <;> cases h
  case case1 =>
    exact wf_of_phase_running hphase hwf
  case case3 =>
    rename_i fields op hcur hsimple
    show Pipeline.WellFormed _
    refine progressTo_wf hwf hcur ?_ True.intro
    show op.kind = .sync ∨ op.kind = .simpleQuery
    exact Or.inr (opKind_eq_of_beq (by simpa [isSimple] using hsimple))
  case case4 =>
    rename_i fields op hcur hnotsimple hsync
    show Pipeline.WellFormed _
    refine progressTo_wf hwf hcur ?_ True.intro
    show op.kind = .sync ∨ op.kind = .simpleQuery
    exact Or.inl (opKind_eq_of_beq hsync)
  case case5 =>
    rename_i fields op hcur hnotsimple hnotsync
    show Pipeline.WellFormed (abortToSync pipe)
    exact abortToSync_wf (aborted_false_of_current hwf hcur)
  case case6 =>
    rename_i tx op hcur hkind
    show Pipeline.WellFormed (advance pipe)
    exact advance_wf (aborted_false_of_current hwf hcur)
  case case10 =>
    rename_i op hcur hguard
    show Pipeline.WellFormed (advance pipe)
    exact advance_wf (aborted_false_of_current hwf hcur)
  case case13 =>
    rename_i op hcur hguard
    show Pipeline.WellFormed (advance pipe)
    exact advance_wf (aborted_false_of_current hwf hcur)
  case case16 =>
    rename_i op hcur hguard
    show Pipeline.WellFormed (advance pipe)
    exact advance_wf (aborted_false_of_current hwf hcur)
  case case19 =>
    rename_i oids op hcur hguard
    show Pipeline.WellFormed _
    refine progressTo_wf hwf hcur ?_ True.intro
    show op.kind = .describeStatement
    exact opKind_eq_of_beq (by
      simp only [Bool.and_eq_true] at hguard
      exact hguard.1)
  case case22 =>
    rename_i columns op hcur hprog hkind
    show Pipeline.WellFormed (advance pipe)
    exact advance_wf (aborted_false_of_current hwf hcur)
  case case23 =>
    rename_i columns op hcur hprog hkind
    show Pipeline.WellFormed (advance pipe)
    exact advance_wf (aborted_false_of_current hwf hcur)
  case case24 =>
    rename_i columns op hcur hprog hkind
    show Pipeline.WellFormed _
    refine progressTo_wf hwf hcur ?_ True.intro
    show op.kind = .simpleQuery
    exact hkind
  case case27 =>
    rename_i op hcur hprog hkind
    show Pipeline.WellFormed (advance pipe)
    exact advance_wf (aborted_false_of_current hwf hcur)
  case case28 =>
    rename_i op hcur hprog hkind
    show Pipeline.WellFormed (advance pipe)
    exact advance_wf (aborted_false_of_current hwf hcur)
  case case31 =>
    rename_i columns op hcur hprog hkind
    show Pipeline.WellFormed _
    refine progressTo_wf hwf hcur ?_ True.intro
    show op.kind = .execute
    exact hkind
  case case32 =>
    rename_i columns op hcur cols hprog hkind
    show Pipeline.WellFormed pipe
    exact hwf
  case case33 =>
    rename_i columns op hcur hkind n hsize hprog
    show Pipeline.WellFormed pipe
    exact hwf
  case case35 =>
    rename_i columns op hcur hkind hprog
    show Pipeline.WellFormed pipe
    exact hwf
  case case38 =>
    rename_i tag op hcur hkind
    show Pipeline.WellFormed (advance pipe)
    exact advance_wf (aborted_false_of_current hwf hcur)
  case case39 =>
    rename_i tag op hcur hkind
    show Pipeline.WellFormed _
    exact progressTo_wf hwf hcur True.intro True.intro
  case case42 =>
    rename_i op hcur hkind
    show Pipeline.WellFormed (advance pipe)
    exact advance_wf (aborted_false_of_current hwf hcur)
  case case43 =>
    rename_i op hcur hkind
    show Pipeline.WellFormed _
    exact progressTo_wf hwf hcur True.intro True.intro
  case case46 =>
    rename_i op hcur hguard
    show Pipeline.WellFormed (advance pipe)
    exact advance_wf (aborted_false_of_current hwf hcur)
  case case49 =>
    rename_i overall formats op hcur hguard hqueue info
    show Pipeline.WellFormed _
    refine progressTo_wf hwf hcur ?_ ?_
    · show op.kind = .execute ∨ op.kind = .simpleQuery
      simp only [Bool.and_eq_true, Bool.or_eq_true] at hguard
      exact hguard.1.imp opKind_eq_of_beq opKind_eq_of_beq
    · show pipe.queued.all (· == OpKind.sync) = true ∧ pipe.queued.size ≤ 1
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hqueue
      exact hqueue
  case case53 =>
    rename_i overall formats op hcur hguard hqueue info
    show Pipeline.WellFormed _
    refine progressTo_wf hwf hcur ?_ True.intro
    show op.kind = .execute ∨ op.kind = .simpleQuery
    simp only [Bool.and_eq_true, Bool.or_eq_true] at hguard
    exact hguard.1.imp opKind_eq_of_beq opKind_eq_of_beq
  case case57 =>
    rename_i data op hcur info hprog
    show Pipeline.WellFormed pipe
    exact hwf
  case case60 =>
    rename_i op hcur info hprog
    show Pipeline.WellFormed _
    exact progressTo_wf hwf hcur True.intro True.intro

/-- The SCRAM-mechanism record the startup invariant tracks. -/
private def StartupMech (s : State) (auth : AuthState) : Prop :=
  match auth with
  | .scram _ => s.negotiatedSaslMechanism.isSome = true
  | _ => True

private theorem startup_parts {s : State} {auth : AuthState}
    (hphase : s.phase = .startup auth) (hwf : s.WellFormed) :
    s.txStatus = .idle ∧ StartupMech s auth := by
  unfold State.WellFormed at hwf
  rw [hphase] at hwf
  exact hwf

private theorem stepStartup_wf {s : State} {auth : AuthState} {m : BackendMsg}
    (hphase : s.phase = .startup auth) (hwf : s.WellFormed) :
    ∀ {s' : State} {evs : Array Event} {out : ByteArray},
      stepStartup s auth m = .ok (s', evs, out) → s'.WellFormed := by
  fun_cases stepStartup s auth m <;> intro s' evs out h <;> cases h
  case case2 => exact ⟨(startup_parts hphase hwf).1, True.intro⟩
  case case3 => exact ⟨(startup_parts hphase hwf).1, True.intro⟩
  case case4 => exact ⟨(startup_parts hphase hwf).1, True.intro⟩
  case case5 => exact ⟨(startup_parts hphase hwf).1, True.intro⟩
  case case8 => exact ⟨(startup_parts hphase hwf).1, True.intro⟩
  case case10 => exact ⟨(startup_parts hphase hwf).1, True.intro⟩
  case case14 => exact ⟨(startup_parts hphase hwf).1, rfl⟩
  case case16 => exact ⟨(startup_parts hphase hwf).1, (startup_parts hphase hwf).2⟩
  case case19 => exact ⟨(startup_parts hphase hwf).1, True.intro⟩
  case case28 => exact hwf
  case case30 => exact hwf
  case case31 => exact hwf
  case case32 => exact hwf
  case case33 => exact hwf
  case case36 => exact emptyPipeline_wf

/-- `step` preserves well-formedness on every accepted backend message. -/
theorem step_wellFormed {s : State} {msg : RawMessage} {s' : State}
    {evs : Array Event} {out : ByteArray}
    (hwf : s.WellFormed) (h : step s msg = .ok (s', evs, out)) : s'.WellFormed := by
  revert h
  fun_cases step s msg
  case case3 => intro h; cases h; exact hwf
  case case4 => intro h; cases h; exact hwf
  case case5 => intro h; cases h; exact hwf
  case case6 =>
    rename_i m hdec auth hph hn1 hn2 hn3
    intro h
    exact stepStartup_wf hph hwf h
  case case7 =>
    rename_i m hdec pipe hph hn1 hn2 hn3
    intro h
    exact stepRunning_wf hph (pipe_wf_of_running hph hwf) h
  all_goals (intro h; cases h)

private theorem runSteps_wf :
    ∀ {msgs : List RawMessage} {s : State} {events : Array Event} {out : ByteArray}
      {r : State × Array Event × ByteArray},
      s.WellFormed → runSteps s msgs events out = .ok r → r.1.WellFormed := by
  intro msgs
  induction msgs with
  | nil =>
    intro s events out r hwf h
    cases h
    exact hwf
  | cons m rest ih =>
    intro s events out r hwf h
    unfold runSteps at h
    cases hst : step s m with
    | error e =>
      rw [hst] at h
      cases h
    | ok res =>
      obtain ⟨s1, evs1, b1⟩ := res
      rw [hst] at h
      exact ih (step_wellFormed hwf hst) h

/-- `feed` preserves well-formedness across a whole chunk of frames. -/
theorem feed_wellFormed {s : State} {chunk : ByteArray} {s' : State}
    {evs : Array Event} {out : ByteArray}
    (hwf : s.WellFormed) (h : feed s chunk = .ok (s', evs, out)) : s'.WellFormed := by
  unfold feed at h
  split at h
  · cases h
  · split at h
    rename_i fed hd msgs decode htake
    exact runSteps_wf (s := { s with decode := decode }) (r := (s', evs, out)) hwf h

/-!
### Bridging framing conservation to the machine

`feed` is the composition of two proved layers: the framing decoder
(`DecodeState.feed`, which conserves bytes — `DecodeState.feed_conservation`)
and per-frame stepping (`runSteps`/`step`, which never touches the decoder).
`feed_frames` makes the factoring explicit: every successful `feed` exhibits
the exact frame sequence it stepped, and re-encoding those frames plus the
retained buffer reproduces the bytes fed. Since `start`, `submit`, and `step`
leave the decoder's drained-message queue empty (`start_messages_drained`,
`submit_decode`, `step_decode`) and `feed` re-drains it
(`feed_messages_drained`), the byte accounting is exact on every reachable
state (`feed_byte_accounting`).
-/

private theorem stepStartup_decode {s : State} {auth : AuthState} {m : BackendMsg}
    {s' : State} {evs : Array Event} {out : ByteArray}
    (h : stepStartup s auth m = .ok (s', evs, out)) : s'.decode = s.decode := by
  revert h
  fun_cases stepStartup s auth m <;> intro h <;> cases h <;> rfl

private theorem stepRunning_decode {s : State} {pipe : Pipeline} {m : BackendMsg}
    {s' : State} {evs : Array Event} {out : ByteArray}
    (h : stepRunning s pipe m = .ok (s', evs, out)) : s'.decode = s.decode := by
  revert h
  fun_cases stepRunning s pipe m <;> intro h <;> cases h <;> rfl

/-- `step` never touches the framing decoder — frame boundaries and message
semantics live in separate layers. -/
theorem step_decode {s : State} {msg : RawMessage} {s' : State} {evs : Array Event}
    {out : ByteArray} (h : step s msg = .ok (s', evs, out)) : s'.decode = s.decode := by
  revert h
  fun_cases step s msg
  case case3 => intro h; cases h; rfl
  case case4 => intro h; cases h; rfl
  case case5 => intro h; cases h; rfl
  case case6 => intro h; exact stepStartup_decode h
  case case7 => intro h; exact stepRunning_decode h
  all_goals (intro h; cases h)

/-- Neither does `submit`. -/
theorem submit_decode {s : State} {req : Request} {s' : State} {out : ByteArray}
    (h : submit s req = .ok (s', out)) : s'.decode = s.decode := by
  have idle : ∀ (s₀ : State) (pipe : Pipeline) (req₀ : Request),
      s₀.decode = s.decode →
      submitIdle s₀ pipe req₀ = .ok (s', out) → s'.decode = s.decode := by
    intro s₀ pipe req₀ hdec
    fun_cases submitIdle s₀ pipe req₀ <;> intro h' <;> cases h' <;> exact hdec
  have running : ∀ (s₀ : State) (pipe : Pipeline) (req₀ : Request),
      s₀.decode = s.decode →
      submitRunning s₀ pipe req₀ = .ok (s', out) → s'.decode = s.decode := by
    intro s₀ pipe req₀ hdec
    fun_cases submitRunning s₀ pipe req₀ <;> intro h' <;>
      first
        | exact idle _ _ _ hdec h'
        | (cases h' <;> exact hdec)
  revert h
  fun_cases submit s req <;> intro h <;>
    first
      | exact running _ _ _ rfl h
      | (cases h <;> rfl)

theorem runSteps_decode :
    ∀ {msgs : List RawMessage} {s : State} {events : Array Event} {out : ByteArray}
      {r : State × Array Event × ByteArray},
      runSteps s msgs events out = .ok r → r.1.decode = s.decode := by
  intro msgs
  induction msgs with
  | nil =>
    intro s events out r h
    cases h
    rfl
  | cons m rest ih =>
    intro s events out r h
    unfold runSteps at h
    cases hst : step s m with
    | error e =>
      rw [hst] at h
      cases h
    | ok res =>
      obtain ⟨s1, evs1, b1⟩ := res
      rw [hst] at h
      rw [ih h, step_decode hst]

theorem start_messages_drained (cfg : Config) :
    (start cfg).1.decode.messages = #[] := by rfl

/-- **Machine/framing bridge**: a successful `feed` factors into one framing
step and pure message stepping — it exhibits the exact frames stepped, leaves
the drained decoder, and conserves bytes: re-encoding the stepped frames plus
the retained buffer reproduces everything buffered plus the chunk. -/
theorem feed_frames {s : State} {chunk : ByteArray} {s' : State} {evs : Array Event}
    {out : ByteArray} (h : feed s chunk = .ok (s', evs, out)) :
    ∃ msgs : Array RawMessage,
      s.decode.feed chunk = .ok { buffered := s'.decode.buffered, messages := msgs } ∧
      runSteps { s with decode := { buffered := s'.decode.buffered } }
        msgs.toList #[] ByteArray.empty = .ok (s', evs, out) ∧
      s'.decode.messages = #[] ∧
      encodeMessages msgs ++ s'.decode.buffered =
        encodeMessages s.decode.messages ++ (s.decode.buffered ++ chunk) := by
  unfold feed at h
  cases hd : s.decode.feed chunk with
  | error e =>
    rw [hd] at h
    cases h
  | ok fed =>
    rw [hd] at h
    simp only [DecodeState.take_eq] at h
    have hdec : s'.decode = { fed with messages := #[] } :=
      runSteps_decode (r := (s', evs, out)) h
    have hbuf : s'.decode.buffered = fed.buffered := by rw [hdec]
    refine ⟨fed.messages, ?_, ?_, ?_, ?_⟩
    · rw [hbuf]
    · rw [hbuf]
      exact h
    · rw [hdec]
    · rw [hbuf]
      exact DecodeState.feed_conservation hd

/-- `feed` re-drains the decoder's completed-message queue. -/
theorem feed_messages_drained {s : State} {chunk : ByteArray} {s' : State}
    {evs : Array Event} {out : ByteArray} (h : feed s chunk = .ok (s', evs, out)) :
    s'.decode.messages = #[] :=
  (feed_frames h).choose_spec.2.2.1

/-- Exact byte accounting on a drained state (every reachable state is one):
the frames the machine stepped, re-encoded, plus the bytes it retained, are
exactly the bytes it was holding plus the chunk it was fed. -/
theorem feed_byte_accounting {s : State} {chunk : ByteArray} {s' : State}
    {evs : Array Event} {out : ByteArray}
    (hm : s.decode.messages = #[]) (h : feed s chunk = .ok (s', evs, out)) :
    ∃ msgs : Array RawMessage,
      encodeMessages msgs ++ s'.decode.buffered = s.decode.buffered ++ chunk := by
  obtain ⟨msgs, -, -, -, hc⟩ := feed_frames h
  refine ⟨msgs, ?_⟩
  rwa [hm, encodeMessages_nil, ByteArray.empty_append] at hc

/-- Async messages (NoticeResponse / ParameterStatus / NotificationResponse)
never advance the pending pipeline: the phase — including the whole op queue
— is untouched, and no protocol bytes are emitted. -/
theorem step_async_preserves_pipeline {s : State} {msg : RawMessage}
    {m : BackendMsg} {s' : State} {evs : Array Event} {out : ByteArray}
    (hdec : Backend.decode msg = .ok m)
    (hasync : (m matches .noticeResponse _ | .parameterStatus .. |
      .notificationResponse ..) = true)
    (h : step s msg = .ok (s', evs, out)) :
    s'.phase = s.phase ∧ out = ByteArray.empty := by
  revert h
  fun_cases step s msg
  case case1 => intro h; cases h
  case case2 =>
    rename_i e hdec'
    rw [hdec] at hdec'
    cases hdec'
  case case3 => intro h; cases h; exact ⟨rfl, rfl⟩
  case case4 => intro h; cases h; exact ⟨rfl, rfl⟩
  case case5 => intro h; cases h; exact ⟨rfl, rfl⟩
  case case6 =>
    rename_i m' hdec' auth hph hn1 hn2 hn3
    rw [hdec] at hdec'
    injection hdec' with hm
    subst hm
    cases m
    case noticeResponse fields => exact absurd rfl (hn1 fields)
    case parameterStatus name value => exact absurd rfl (hn2 name value)
    case notificationResponse pid ch pl => exact absurd rfl (hn3 pid ch pl)
    all_goals exact nomatch hasync
  case case7 =>
    rename_i m' hdec' pipe hph hn1 hn2 hn3
    rw [hdec] at hdec'
    injection hdec' with hm
    subst hm
    cases m
    case noticeResponse fields => exact absurd rfl (hn1 fields)
    case parameterStatus name value => exact absurd rfl (hn2 name value)
    case notificationResponse pid ch pl => exact absurd rfl (hn3 pid ch pl)
    all_goals exact nomatch hasync
  case case8 =>
    rename_i m' hdec' hph hn1 hn2 hn3
    intro h
    cases h

/-!
### Progress

Preservation alone would be satisfied by a machine that rejects everything.
`step_progress` rules that out: whenever the pipeline's head op awaits a
reply and the backend sends a message of the expected class, `step` succeeds
(no `.ok` obligations beyond decoding — not even `WellFormed`). The expected
classes are exactly PostgreSQL's documented reply sets per request type.
`step_errorResponse_progress` complements it: an ErrorResponse is always
accepted while an op is pending — server errors during a pipeline can never
poison the connection.
-/

/-- Backend messages that legitimately answer the pipeline's head op in its
current reply-progress state. Async messages are always accepted
(`step_async_preserves_pipeline`), ErrorResponse is always accepted while an
op is pending (`step_errorResponse_progress`), and the COPY-start responses
additionally depend on the queued pipeline, so they are not listed here. -/
def ExpectedReply (op : CurrentOp) (m : BackendMsg) : Prop :=
  match op.kind, op.progress, m with
  | .parse, .start, .parseComplete => True
  | .bind, .start, .bindComplete => True
  | .close, .start, .closeComplete => True
  | .describeStatement, .start, .parameterDescription _ => True
  | .describeStatement, .descParams, .rowDescription _ => True
  | .describeStatement, .descParams, .noData => True
  | .describePortal, .start, .rowDescription _ => True
  | .describePortal, .start, .noData => True
  | .execute, .start, .dataRow _ => True
  | .execute, .rows none, .dataRow _ => True
  | .execute, .start, .commandComplete _ => True
  | .execute, .rows none, .commandComplete _ => True
  | .execute, .start, .emptyQueryResponse => True
  | .execute, .start, .portalSuspended => True
  | .execute, .rows none, .portalSuspended => True
  | .sync, _, .readyForQuery _ => True
  | .simpleQuery, .start, .rowDescription _ => True
  | .simpleQuery, .start, .commandComplete _ => True
  | .simpleQuery, .start, .emptyQueryResponse => True
  | .simpleQuery, .start, .readyForQuery _ => True
  | .simpleQuery, .rows (some n), .dataRow cols => cols.size = n
  | .simpleQuery, .rows _, .commandComplete _ => True
  | .simpleQuery, .rows _, .readyForQuery _ => True
  | _, .copyOut _, .copyData _ => True
  | _, .copyOut _, .copyDone => True
  | _, _, _ => False

/-- **Progress**: an expected reply for the head op always steps successfully. -/
theorem step_progress {s : State} {pipe : Pipeline} {op : CurrentOp}
    {msg : RawMessage} {m : BackendMsg}
    (hph : s.phase = .running pipe) (hcur : pipe.current = some op)
    (hdec : Backend.decode msg = .ok m) (hexp : ExpectedReply op m) :
    ∃ r, step s msg = .ok r := by
  revert hexp
  fun_cases ExpectedReply op m <;> intro hexp <;>
    first
      | exact hexp.elim
      | (unfold step stepRunning
         simp only [*, beq_self_eq_true]
         exact ⟨_, rfl⟩)

/-- An ErrorResponse is always accepted while an op is pending: recoverable
server errors can never poison a mid-pipeline connection. -/
theorem step_errorResponse_progress {s : State} {pipe : Pipeline} {op : CurrentOp}
    {msg : RawMessage} {fields : ErrorFields}
    (hph : s.phase = .running pipe) (hcur : pipe.current = some op)
    (hdec : Backend.decode msg = .ok (.errorResponse fields)) :
    ∃ r, step s msg = .ok r := by
  cases hsimple : isSimple op <;> cases hsync : op.kind == OpKind.sync <;>
    (unfold step stepRunning
     simp only [hph, hdec, hcur, hsimple, hsync]
     exact ⟨_, rfl⟩)

/-!
### Error/Sync recovery attribution

After an extended-protocol `ErrorResponse`, PostgreSQL discards frontend
messages until a Sync. These theorems pin down the client-side mirror of that
rule, so no backend response can ever be attributed to the wrong request:

- `dropAborted_found`/`dropAborted_none`: the cancellation rule partitions the
  queue exactly at the first Sync — every dropped expectation is accounted
  for, and none of the dropped ones was a recovery boundary.
- `error_enters_drain_until_sync`: an error on an extended-protocol head op
  moves the machine to `abortToSync pipe` and emits exactly the error event.
- `abortToSync_found`/`abortToSync_none`: the post-error pipeline is exactly
  "drain to the first queued Sync" or "fully aborted awaiting a user Sync".
- `drained_operation_cannot_succeed`: while draining, the machine accepts
  *only* ReadyForQuery, further errors, and async messages — no
  operation-success message can be mis-attributed to a cancelled op.
- `readyForQuery_clears_recovery_state` /
  `readyForQuery_restores_pipeline_alignment`: the Sync's ReadyForQuery pops
  the draining head and promotes exactly the next queued op, fresh at
  `.start`, in queue order.
- `sync_clears_aborted`: on a fully aborted pipeline, submitting Sync is
  accepted, re-arms the pipeline with exactly that Sync pending, and writes
  the Sync bytes.

These are the per-step cases of the trace-level FIFO refinement proved in the
next section (`step_fifo`, `runSteps_fifo`, `feed_fifo`, `submit_fifo`).
-/

private theorem opKind_beq_eq_false {a b : OpKind} (h : a ≠ b) : (a == b) = false := by
  cases hab : a == b
  · rfl
  · exact absurd (opKind_eq_of_beq hab) h

/-- `dropAborted` found a Sync: the queue splits exactly there — every dropped
entry precedes it and is not a Sync, and the remainder starts with it. -/
theorem dropAborted_found {α : Type} {isSync : α → Bool} {queue rest : Array α}
    (h : dropAborted isSync queue = (rest, true)) :
    ∃ i, ∃ (hi : i < queue.size),
      isSync (queue[i]'hi) = true ∧
      (∀ j (hj : j < i), isSync (queue[j]'(Nat.lt_trans hj hi)) = false) ∧
      rest = queue.extract i queue.size ∧
      queue.extract 0 i ++ rest = queue := by
  unfold dropAborted at h
  cases hf : queue.findIdx? isSync with
  | none =>
    rw [hf] at h
    injection h with _ h2
    cases h2
  | some i =>
    rw [hf] at h
    injection h with h1 _
    obtain ⟨hi, hp, hmin⟩ := Array.findIdx?_eq_some_iff_getElem.mp hf
    refine ⟨i, hi, hp, ?_, h1.symm, ?_⟩
    · intro j hj
      have := hmin j hj
      rwa [Bool.not_eq_true] at this
    · rw [← h1, Array.extract_append_extract,
        Nat.min_eq_left (Nat.zero_le i), Nat.max_eq_right (Nat.le_of_lt hi)]
      exact Array.extract_size

/-- `dropAborted` found no Sync: everything is dropped and indeed none of the
queued expectations was a recovery boundary. -/
theorem dropAborted_none {α : Type} {isSync : α → Bool} {queue rest : Array α}
    (h : dropAborted isSync queue = (rest, false)) :
    rest = #[] ∧ ∀ x ∈ queue, isSync x = false := by
  unfold dropAborted at h
  cases hf : queue.findIdx? isSync with
  | none =>
    rw [hf] at h
    injection h with h1 _
    exact ⟨h1.symm, Array.findIdx?_eq_none_iff.mp hf⟩
  | some i =>
    rw [hf] at h
    injection h with _ h2
    cases h2

/-- An extended-protocol error (head op is neither simpleQuery nor Sync)
moves the machine to exactly `abortToSync pipe`, emits exactly the error
event, and writes nothing. -/
theorem error_enters_drain_until_sync {s : State} {pipe : Pipeline} {op : CurrentOp}
    {msg : RawMessage} {fields : ErrorFields} {s' : State} {evs : Array Event}
    {out : ByteArray}
    (hph : s.phase = .running pipe) (hcur : pipe.current = some op)
    (hnotsimple : op.kind ≠ .simpleQuery) (hnotsync : op.kind ≠ .sync)
    (hdec : Backend.decode msg = .ok (.errorResponse fields))
    (h : step s msg = .ok (s', evs, out)) :
    s'.phase = .running (abortToSync pipe) ∧ evs = #[.errorResponse fields] ∧
      out = ByteArray.empty := by
  unfold step stepRunning at h
  simp only [hph, hdec, hcur, isSimple, opKind_beq_eq_false hnotsimple,
    opKind_beq_eq_false hnotsync] at h
  cases h
  exact ⟨rfl, rfl, rfl⟩

/-- The post-error pipeline when a Sync was queued at index `i`: everything
before it is dropped (none of it a Sync), the Sync becomes the draining head,
and the queue resumes right after it. -/
theorem abortToSync_found {pipe : Pipeline} {i : Nat} (hi : i < pipe.queued.size)
    (hsync : pipe.queued[i]'hi = .sync)
    (hbefore : ∀ j (hj : j < i), pipe.queued[j]'(Nat.lt_trans hj hi) ≠ .sync) :
    abortToSync pipe =
      { pipe with
        current := some { kind := .sync, progress := .drainError }
        queued := pipe.queued.extract (i + 1) pipe.queued.size } := by
  unfold abortToSync
  cases hd : dropAborted (· == OpKind.sync) pipe.queued with
  | mk rest found =>
    cases found with
    | false =>
      obtain ⟨-, hall⟩ := dropAborted_none hd
      have := hall (pipe.queued[i]'hi) (Array.getElem_mem hi)
      rw [hsync] at this
      cases this
    | true =>
      obtain ⟨i', hi', hp', hmin', hrest, -⟩ := dropAborted_found hd
      have hii : i' = i := by
        rcases Nat.lt_trichotomy i' i with hlt | heq | hgt
        · exact absurd (opKind_eq_of_beq hp') (hbefore i' hlt)
        · exact heq
        · have := hmin' i hgt
          rw [hsync] at this
          cases this
      subst hii hrest
      simp only
      congr 1
      rw [Array.extract_extract]
      congr 1
      have hsz : (pipe.queued.extract i' pipe.queued.size).size =
          pipe.queued.size - i' := by
        rw [Array.size_extract, Nat.min_eq_right (Nat.le_refl _)]
      rw [hsz]
      omega

/-- The post-error pipeline when no Sync was queued: every queued expectation
is dropped and the pipeline is gated (`aborted`) until the user submits a
Sync. -/
theorem abortToSync_none {pipe : Pipeline}
    (hnone : ∀ k, k ∈ pipe.queued → k ≠ OpKind.sync) :
    abortToSync pipe = { pipe with current := none, queued := #[], aborted := true } := by
  unfold abortToSync
  cases hd : dropAborted (· == OpKind.sync) pipe.queued with
  | mk rest found =>
    cases found with
    | false => rfl
    | true =>
      obtain ⟨i, hi, hp, -, -, -⟩ := dropAborted_found hd
      exact absurd (opKind_eq_of_beq hp) (hnone _ (Array.getElem_mem hi))

/-- While the head is a draining Sync, the machine accepts **only**
ReadyForQuery (ending recovery), further ErrorResponses, and async messages.
Every operation-success message is rejected, so no backend success can be
attributed to a cancelled operation. -/
theorem drained_operation_cannot_succeed {s : State} {pipe : Pipeline}
    {op : CurrentOp} {msg : RawMessage} {m : BackendMsg} {s' : State}
    {evs : Array Event} {out : ByteArray}
    (hph : s.phase = .running pipe) (hcur : pipe.current = some op)
    (hkind : op.kind = .sync) (hprog : op.progress = .drainError)
    (hdec : Backend.decode msg = .ok m)
    (h : step s msg = .ok (s', evs, out)) :
    (∃ tx, m = .readyForQuery tx) ∨ (∃ f, m = .errorResponse f) ∨
    (∃ f, m = .noticeResponse f) ∨ (∃ n v, m = .parameterStatus n v) ∨
    (∃ p c pl, m = .notificationResponse p c pl) := by
  cases m <;>
    first
      | exact Or.inl ⟨_, rfl⟩
      | exact Or.inr (Or.inl ⟨_, rfl⟩)
      | exact Or.inr (Or.inr (Or.inl ⟨_, rfl⟩))
      | exact Or.inr (Or.inr (Or.inr (Or.inl ⟨_, _, rfl⟩)))
      | exact Or.inr (Or.inr (Or.inr (Or.inr ⟨_, _, _, rfl⟩)))
      | (unfold step stepRunning at h
         simp +decide [hph, hdec, hcur, hkind, hprog] at h)

/-- ReadyForQuery on a Sync/simpleQuery head ends its cycle: the head —
draining or not — is popped, the transaction status is adopted, exactly one
`ready` event is emitted, and nothing is written. -/
theorem readyForQuery_clears_recovery_state {s : State} {pipe : Pipeline}
    {op : CurrentOp} {msg : RawMessage} {tx : TxStatus} {s' : State}
    {evs : Array Event} {out : ByteArray}
    (hph : s.phase = .running pipe) (hcur : pipe.current = some op)
    (hkind : op.kind = .sync ∨ op.kind = .simpleQuery)
    (hdec : Backend.decode msg = .ok (.readyForQuery tx))
    (h : step s msg = .ok (s', evs, out)) :
    s'.phase = .running (advance pipe) ∧ s'.txStatus = tx ∧
      evs = #[.ready tx] ∧ out = ByteArray.empty := by
  have hguard : (op.kind == OpKind.sync || op.kind == OpKind.simpleQuery) = true := by
    cases hkind with
    | inl hk => rw [hk]; rfl
    | inr hk => rw [hk]; rfl
  unfold step stepRunning at h
  simp only [hph, hdec, hcur, hguard] at h
  cases h
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- Alignment after ReadyForQuery: the promoted head is exactly the next
queued op — fresh at `.start` — and the rest of the queue keeps its order
(or the pipeline is idle when nothing was queued). The abort gate is
untouched. -/
theorem readyForQuery_restores_pipeline_alignment {s : State} {pipe : Pipeline}
    {op : CurrentOp} {msg : RawMessage} {tx : TxStatus} {s' : State}
    {evs : Array Event} {out : ByteArray}
    (hph : s.phase = .running pipe) (hcur : pipe.current = some op)
    (hkind : op.kind = .sync ∨ op.kind = .simpleQuery)
    (hdec : Backend.decode msg = .ok (.readyForQuery tx))
    (h : step s msg = .ok (s', evs, out)) :
    s'.phase = .running (advance pipe) ∧
    (advance pipe).aborted = pipe.aborted ∧
    ((∃ (h0 : 0 < pipe.queued.size),
        (advance pipe).current = some { kind := pipe.queued[0]'h0 } ∧
        (advance pipe).queued = pipe.queued.extract 1 pipe.queued.size) ∨
      (pipe.queued = #[] ∧ (advance pipe).current = none ∧
        (advance pipe).queued = #[])) := by
  refine ⟨(readyForQuery_clears_recovery_state hph hcur hkind hdec h).1, ?_, ?_⟩
  · unfold advance
    cases hq : pipe.queued[0]? <;> rfl
  · unfold advance
    cases hq : pipe.queued[0]? with
    | none =>
      have hqe : pipe.queued = #[] := by
        have := Array.getElem?_eq_none_iff.mp hq
        exact Array.eq_empty_of_size_eq_zero (by omega)
      exact Or.inr ⟨hqe, rfl, hqe⟩
    | some k =>
      obtain ⟨h0, hk⟩ := Array.getElem?_eq_some_iff.mp hq
      exact Or.inl ⟨h0, by rw [hk], rfl⟩

/-- Submitting Sync on a fully aborted pipeline is accepted: the gate clears,
exactly that Sync becomes the pending head, and the Sync bytes are written. -/
theorem sync_clears_aborted {s : State} {pipe : Pipeline} {s' : State}
    {out : ByteArray}
    (hph : s.phase = .running pipe) (hab : pipe.aborted = true) (hwf : s.WellFormed)
    (h : submit s .sync = .ok (s', out)) :
    s'.phase = .running
      { current := some { kind := .sync }, queued := #[], aborted := false } ∧
    out = Frontend.sync := by
  obtain ⟨hc, hq⟩ := (pipe_wf_of_running hph hwf).1 hab
  unfold submit submitRunning submitIdle enqueue at h
  simp only [hph, hc, hab] at h
  cases h
  refine ⟨?_, rfl⟩
  show Phase.running _ = _
  congr 1
  simp only [hq]

/-!
### Trace-level FIFO attribution

The shell keeps its own FIFO of user-facing completions, sees only the event
stream, and applies two rules: pop the head on its terminal reply, and drop to
the next pipelined Sync on an extended-protocol error. `shellStep` *is* that
rule. `Pipeline.pending` is the same FIFO as the machine sees it — the ops
still awaiting replies, in submission order.

`step_fifo` / `runSteps_fifo` / `feed_fifo` prove the two agree on every
accepted message, and `submit_fifo` proves submissions only ever append (one
entry per accepted request, in submission order). Together they are the FIFO
refinement: the shell's event-driven queue is always exactly the machine's
pending-op queue, so no reply can be attributed to the wrong request.
`terminal_pops_head` reads off the headline — every user-visible success is
the terminal reply of the op at the FIFO head and pops exactly that one op —
and `nonterminal_preserves_fifo` its complement.
-/

/-- The correlation FIFO as the machine sees it: the ops still awaiting
replies, in submission order (head first). -/
def Pipeline.pending (pipe : Pipeline) : List OpKind :=
  match pipe.current with
  | some op => op.kind :: pipe.queued.toList
  | none => pipe.queued.toList

/-- The user-visible terminal reply of an op kind: the event on which the
shell completes that op and pops it from its FIFO. Every other event either
reports intermediate progress on the head op (`parameterDescription`,
`dataRow`, `copyInStarted`, a simple query's per-statement `commandComplete`,
...), is an error, or is asynchronous. -/
def isTerminal : OpKind → Event → Bool
  | .parse, .parseComplete => true
  | .bind, .bindComplete => true
  | .close, .closeComplete => true
  | .describeStatement, .rowDescription _ => true
  | .describeStatement, .noData => true
  | .describePortal, .rowDescription _ => true
  | .describePortal, .noData => true
  | .execute, .commandComplete _ => true
  | .execute, .emptyQuery => true
  | .execute, .portalSuspended => true
  | .sync, .ready _ => true
  | .simpleQuery, .ready _ => true
  | _, _ => false

/-- Recoverable server errors are the only events that cancel expectations. -/
def isRecoverableError : Event → Bool
  | .errorResponse _ => true
  | _ => false

/-- The FIFO suffix an extended-protocol error preserves: from the first
pipelined Sync on, or nothing when none was pipelined. The list mirror of
`dropAborted` (`abortToSync_pending`). -/
def dropUntilSync : List OpKind → List OpKind
  | [] => []
  | k :: rest => if k == OpKind.sync then k :: rest else dropUntilSync rest

/-- One shell-side FIFO transition, driven by an event alone. -/
def shellStep (fifo : List OpKind) (ev : Event) : List OpKind :=
  match fifo with
  | [] => []
  | k :: rest =>
    if isTerminal k ev then rest
    else if isRecoverableError ev && !(k == OpKind.sync) && !(k == OpKind.simpleQuery) then
      dropUntilSync rest
    else k :: rest

/-- The shell's FIFO after a batch of events, in wire order. -/
def shellRun (fifo : List OpKind) (evs : Array Event) : List OpKind :=
  evs.foldl shellStep fifo

private theorem shellRun_single (fifo : List OpKind) (ev : Event) :
    shellRun fifo #[ev] = shellStep fifo ev := by rfl

private theorem shellRun_append (fifo : List OpKind) (a b : Array Event) :
    shellRun fifo (a ++ b) = shellRun (shellRun fifo a) b := by
  unfold shellRun
  exact Array.foldl_append

private theorem shellStep_pop {k : OpKind} {rest : List OpKind} {ev : Event}
    (hterm : isTerminal k ev = true) : shellStep (k :: rest) ev = rest := by
  unfold shellStep
  simp only [hterm, if_pos]

private theorem shellStep_keep {k : OpKind} {rest : List OpKind} {ev : Event}
    (hterm : isTerminal k ev = false) (herr : isRecoverableError ev = false) :
    shellStep (k :: rest) ev = k :: rest := by
  unfold shellStep
  simp only [hterm, herr, Bool.false_and, Bool.false_eq_true, if_false]

private theorem shellStep_keep_all {fifo : List OpKind} {ev : Event}
    (hterm : ∀ k, isTerminal k ev = false) (herr : isRecoverableError ev = false) :
    shellStep fifo ev = fifo := by
  cases fifo with
  | nil => rfl
  | cons k rest => exact shellStep_keep (hterm k) herr

private theorem shellStep_drain {k : OpKind} {rest : List OpKind} {f : ErrorFields}
    (hk : k = .sync ∨ k = .simpleQuery) :
    shellStep (k :: rest) (.errorResponse f) = k :: rest := by
  unfold shellStep
  cases hk with
  | inl h => subst h; rfl
  | inr h => subst h; rfl

private theorem shellStep_abort {k : OpKind} {rest : List OpKind} {f : ErrorFields}
    (hsync : (k == OpKind.sync) = false) (hsimple : (k == OpKind.simpleQuery) = false) :
    shellStep (k :: rest) (.errorResponse f) = dropUntilSync rest := by
  unfold shellStep
  have hterm : isTerminal k (.errorResponse f) = false := by cases k <;> rfl
  simp only [hterm, hsync, hsimple, isRecoverableError, Bool.not_false, Bool.and_true,
    Bool.false_eq_true, if_false, if_pos]

private theorem shellStep_nil (ev : Event) : shellStep [] ev = [] := by rfl

private theorem toList_extract_size {α : Type} (a : Array α) (i : Nat) :
    (a.extract i a.size).toList = a.toList.drop i := by
  rw [Array.toList_extract, List.extract_eq_take_drop, ← Array.length_toList,
    ← List.length_drop (i := i) (l := a.toList)]
  exact List.take_length

private theorem cons_drop_one {α : Type} {l : List α} {k : α} (h : l[0]? = some k) :
    k :: l.drop 1 = l := by
  cases l with
  | nil => cases h
  | cons a t =>
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    rw [h]
    rfl

private theorem pending_cons {pipe : Pipeline} {op : CurrentOp}
    (hcur : pipe.current = some op) :
    pipe.pending = op.kind :: pipe.queued.toList := by
  unfold Pipeline.pending
  rw [hcur]

private theorem pending_nil {pipe : Pipeline} (hcur : pipe.current = none)
    (hq : pipe.queued = #[]) : pipe.pending = [] := by
  unfold Pipeline.pending
  rw [hcur, hq]

private theorem progressTo_pending {pipe : Pipeline} {op : CurrentOp} {p : Progress} :
    ({ pipe with current := some { op with progress := p } } : Pipeline).pending
      = op.kind :: pipe.queued.toList := by rfl

/-- Popping the head promotes the queue verbatim: the FIFO loses exactly its
head entry. -/
theorem advance_pending (pipe : Pipeline) :
    (advance pipe).pending = pipe.queued.toList := by
  unfold advance
  split
  · next k hq =>
    show k :: (pipe.queued.extract 1 pipe.queued.size).toList = pipe.queued.toList
    rw [toList_extract_size]
    exact cons_drop_one (by rw [Array.getElem?_toList]; exact hq)
  · next hq =>
    have hqe : pipe.queued = #[] :=
      Array.eq_empty_of_size_eq_zero (by
        have := Array.getElem?_eq_none_iff.mp hq
        omega)
    show (pipe.queued.toList : List OpKind) = pipe.queued.toList
    rfl

private theorem dropUntilSync_none {l : List OpKind} (h : ∀ k ∈ l, k ≠ OpKind.sync) :
    dropUntilSync l = [] := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    unfold dropUntilSync
    rw [if_neg (by
      intro hb
      exact h a (List.mem_cons_self ..) (opKind_eq_of_beq hb))]
    exact ih (fun k hk => h k (List.mem_cons_of_mem _ hk))

private theorem dropUntilSync_index : ∀ {l : List OpKind} {i : Nat} (hi : i < l.length),
    l[i] = OpKind.sync → (∀ j (hj : j < i), l[j]'(Nat.lt_trans hj hi) ≠ OpKind.sync) →
    dropUntilSync l = l.drop i := by
  intro l
  induction l with
  | nil => intro i hi; exact absurd hi (by simp)
  | cons a t ih =>
    intro i hi hsync hmin
    cases i with
    | zero =>
      simp only [List.getElem_cons_zero] at hsync
      unfold dropUntilSync
      rw [if_pos (by rw [hsync]; rfl)]
      rfl
    | succ i' =>
      have ha : a ≠ OpKind.sync := by
        have := hmin 0 (Nat.succ_pos i')
        simpa using this
      unfold dropUntilSync
      rw [if_neg (by intro hb; exact ha (opKind_eq_of_beq hb))]
      have hi' : i' < t.length := by simpa using hi
      refine ih hi' ?_ ?_
      · simpa using hsync
      · intro j hj
        have := hmin (j + 1) (Nat.succ_lt_succ hj)
        simpa using this

/-- The post-error pipeline's FIFO is exactly the shell's drop rule applied to
the queue: everything up to the next pipelined Sync is cancelled. -/
theorem abortToSync_pending (pipe : Pipeline) :
    (abortToSync pipe).pending = dropUntilSync pipe.queued.toList := by
  unfold abortToSync
  cases hd : dropAborted (· == OpKind.sync) pipe.queued with
  | mk rest found =>
    cases found with
    | false =>
      obtain ⟨hrest, hall⟩ := dropAborted_none hd
      show ([] : List OpKind) = _
      refine (dropUntilSync_none ?_).symm
      intro k hk
      intro hks
      have := hall k (Array.mem_def.mpr hk)
      rw [hks] at this
      cases this
    | true =>
      obtain ⟨i, hi, hp, hmin, hrest, -⟩ := dropAborted_found hd
      have hli : pipe.queued.toList[i]'(by simpa using hi) = OpKind.sync := by
        rw [Array.getElem_toList]
        exact opKind_eq_of_beq hp
      have hlmin : ∀ j (hj : j < i),
          pipe.queued.toList[j]'(Nat.lt_trans hj (by simpa using hi)) ≠ OpKind.sync := by
        intro j hj hks
        rw [Array.getElem_toList] at hks
        have := hmin j hj
        rw [hks] at this
        cases this
      rw [dropUntilSync_index (by simpa using hi) hli hlmin]
      show OpKind.sync :: (rest.extract 1 rest.size).toList = _
      rw [toList_extract_size, hrest, toList_extract_size]
      refine cons_drop_one ?_
      rw [List.getElem?_drop, Nat.add_zero,
        List.getElem?_eq_getElem (by simpa using hi), hli]

private theorem stepRunning_fifo {s : State} {pipe : Pipeline} {m : BackendMsg}
    (hph : s.phase = .running pipe) (hwf : pipe.WellFormed) :
    ∀ {s' : State} {evs : Array Event} {out : ByteArray},
      stepRunning s pipe m = .ok (s', evs, out) →
      ∃ pipe', s'.phase = .running pipe' ∧ pipe'.pending = shellRun pipe.pending evs := by
  fun_cases stepRunning s pipe m <;> intro s' evs out h <;> cases h
  case case1 =>
    rename_i fields hcur habt
    refine ⟨pipe, hph, ?_⟩
    rw [shellRun_single, pending_nil hcur (hwf.1 habt).2, shellStep_nil]
  case case3 =>
    rename_i fields op hcur hsimple
    refine ⟨_, rfl, ?_⟩
    rw [progressTo_pending, shellRun_single, pending_cons hcur]
    refine (shellStep_drain (Or.inr ?_)).symm
    unfold isSimple at hsimple
    exact opKind_eq_of_beq hsimple
  case case4 =>
    rename_i fields op hcur hnotsimple hsync
    refine ⟨_, rfl, ?_⟩
    rw [progressTo_pending, shellRun_single, pending_cons hcur]
    exact (shellStep_drain (Or.inl (opKind_eq_of_beq hsync))).symm
  case case5 =>
    rename_i fields op hcur hnotsimple hnotsync
    refine ⟨_, rfl, ?_⟩
    rw [abortToSync_pending, shellRun_single, pending_cons hcur]
    unfold isSimple at hnotsimple
    exact (shellStep_abort (Bool.eq_false_iff.mpr hnotsync)
      (Bool.eq_false_iff.mpr hnotsimple)).symm
  case case6 =>
    rename_i tx op hcur hkind
    refine ⟨_, rfl, ?_⟩
    rw [advance_pending, shellRun_single, pending_cons hcur]
    refine (shellStep_pop ?_).symm
    simp only [Bool.or_eq_true] at hkind
    cases hkind.imp opKind_eq_of_beq opKind_eq_of_beq with
    | inl hk => rw [hk]; rfl
    | inr hk => rw [hk]; rfl
  case case10 =>
    rename_i op hcur hguard
    refine ⟨_, rfl, ?_⟩
    rw [advance_pending, shellRun_single, pending_cons hcur]
    refine (shellStep_pop ?_).symm
    simp only [Bool.and_eq_true] at hguard
    rw [opKind_eq_of_beq hguard.1]
    rfl
  case case13 =>
    rename_i op hcur hguard
    refine ⟨_, rfl, ?_⟩
    rw [advance_pending, shellRun_single, pending_cons hcur]
    refine (shellStep_pop ?_).symm
    simp only [Bool.and_eq_true] at hguard
    rw [opKind_eq_of_beq hguard.1]
    rfl
  case case16 =>
    rename_i op hcur hguard
    refine ⟨_, rfl, ?_⟩
    rw [advance_pending, shellRun_single, pending_cons hcur]
    refine (shellStep_pop ?_).symm
    simp only [Bool.and_eq_true] at hguard
    rw [opKind_eq_of_beq hguard.1]
    rfl
  case case19 =>
    rename_i oids op hcur hguard
    refine ⟨_, rfl, ?_⟩
    rw [progressTo_pending, shellRun_single, pending_cons hcur]
    exact (shellStep_keep_all (fun k => by cases k <;> rfl) rfl).symm
  case case22 =>
    rename_i columns op hcur hprog hkind
    refine ⟨_, rfl, ?_⟩
    rw [advance_pending, shellRun_single, pending_cons hcur]
    refine (shellStep_pop ?_).symm
    rw [hkind]
    rfl
  case case23 =>
    rename_i columns op hcur hprog hkind
    refine ⟨_, rfl, ?_⟩
    rw [advance_pending, shellRun_single, pending_cons hcur]
    refine (shellStep_pop ?_).symm
    rw [hkind]
    rfl
  case case24 =>
    rename_i columns op hcur hprog hkind
    refine ⟨_, rfl, ?_⟩
    rw [progressTo_pending, shellRun_single, pending_cons hcur]
    refine (shellStep_keep ?_ rfl).symm
    rw [hkind]
    rfl
  case case27 =>
    rename_i op hcur hprog hkind
    refine ⟨_, rfl, ?_⟩
    rw [advance_pending, shellRun_single, pending_cons hcur]
    refine (shellStep_pop ?_).symm
    rw [hkind]
    rfl
  case case28 =>
    rename_i op hcur hprog hkind
    refine ⟨_, rfl, ?_⟩
    rw [advance_pending, shellRun_single, pending_cons hcur]
    refine (shellStep_pop ?_).symm
    rw [hkind]
    rfl
  case case31 =>
    rename_i columns op hcur hprog hkind
    refine ⟨_, rfl, ?_⟩
    rw [progressTo_pending, shellRun_single, pending_cons hcur]
    exact (shellStep_keep_all (fun k => by cases k <;> rfl) rfl).symm
  case case32 =>
    rename_i columns op hcur cols hprog hkind
    refine ⟨_, rfl, ?_⟩
    rw [shellRun_single]
    exact (shellStep_keep_all (fun k => by cases k <;> rfl) rfl).symm
  case case33 =>
    rename_i columns op hcur hkind n hsize hprog
    refine ⟨_, rfl, ?_⟩
    rw [shellRun_single]
    exact (shellStep_keep_all (fun k => by cases k <;> rfl) rfl).symm
  case case35 =>
    rename_i columns op hcur hkind hprog
    refine ⟨_, rfl, ?_⟩
    rw [shellRun_single]
    exact (shellStep_keep_all (fun k => by cases k <;> rfl) rfl).symm
  case case38 =>
    rename_i tag op hcur hkind
    refine ⟨_, rfl, ?_⟩
    rw [advance_pending, shellRun_single, pending_cons hcur]
    refine (shellStep_pop ?_).symm
    rw [hkind]
    rfl
  case case39 =>
    rename_i tag op hcur hkind
    refine ⟨_, rfl, ?_⟩
    rw [progressTo_pending, shellRun_single, pending_cons hcur]
    refine (shellStep_keep ?_ rfl).symm
    rw [hkind]
    rfl
  case case42 =>
    rename_i op hcur hkind
    refine ⟨_, rfl, ?_⟩
    rw [advance_pending, shellRun_single, pending_cons hcur]
    refine (shellStep_pop ?_).symm
    rw [hkind]
    rfl
  case case43 =>
    rename_i op hcur hkind
    refine ⟨_, rfl, ?_⟩
    rw [progressTo_pending, shellRun_single, pending_cons hcur]
    refine (shellStep_keep ?_ rfl).symm
    rw [hkind]
    rfl
  case case46 =>
    rename_i op hcur hguard
    refine ⟨_, rfl, ?_⟩
    rw [advance_pending, shellRun_single, pending_cons hcur]
    refine (shellStep_pop ?_).symm
    rw [opKind_eq_of_beq hguard]
    rfl
  case case49 =>
    rename_i overall formats op hcur hguard hqueue info
    refine ⟨_, rfl, ?_⟩
    rw [progressTo_pending, shellRun_single, pending_cons hcur]
    exact (shellStep_keep_all (fun k => by cases k <;> rfl) rfl).symm
  case case53 =>
    rename_i overall formats op hcur hguard hqueue info
    refine ⟨_, rfl, ?_⟩
    rw [progressTo_pending, shellRun_single, pending_cons hcur]
    exact (shellStep_keep_all (fun k => by cases k <;> rfl) rfl).symm
  case case57 =>
    rename_i data op hcur info hprog
    refine ⟨_, rfl, ?_⟩
    rw [shellRun_single]
    exact (shellStep_keep_all (fun k => by cases k <;> rfl) rfl).symm
  case case60 =>
    rename_i op hcur info hprog
    refine ⟨_, rfl, ?_⟩
    rw [progressTo_pending, shellRun_single, pending_cons hcur]
    exact (shellStep_keep_all (fun k => by cases k <;> rfl) rfl).symm

/-- **FIFO refinement, one message**: from a well-formed running state, the
machine's pending-op queue evolves exactly as the shell's purely event-driven
FIFO does (and the connection stays in the running phase). -/
theorem step_fifo {s : State} {pipe : Pipeline} {msg : RawMessage} {s' : State}
    {evs : Array Event} {out : ByteArray}
    (hph : s.phase = .running pipe) (hwf : pipe.WellFormed)
    (h : step s msg = .ok (s', evs, out)) :
    ∃ pipe', s'.phase = .running pipe' ∧ pipe'.pending = shellRun pipe.pending evs := by
  revert h
  fun_cases step s msg
  case case3 =>
    intro h
    cases h
    exact ⟨pipe, hph, by
      rw [shellRun_single]
      exact (shellStep_keep_all (fun k => by cases k <;> rfl) rfl).symm⟩
  case case4 =>
    intro h
    cases h
    exact ⟨pipe, hph, by
      rw [shellRun_single]
      exact (shellStep_keep_all (fun k => by cases k <;> rfl) rfl).symm⟩
  case case5 =>
    intro h
    cases h
    exact ⟨pipe, hph, by
      rw [shellRun_single]
      exact (shellStep_keep_all (fun k => by cases k <;> rfl) rfl).symm⟩
  case case6 =>
    rename_i m hdec auth hph2 hn1 hn2 hn3
    rw [hph] at hph2
    cases hph2
  case case7 =>
    rename_i m hdec pipe2 hph2 hn1 hn2 hn3
    rw [hph] at hph2
    injection hph2 with hp
    subst hp
    intro h
    exact stepRunning_fifo hph hwf h
  all_goals (intro h; cases h)

private theorem runSteps_fifo_aux :
    ∀ {msgs : List RawMessage} {s : State} {pipe : Pipeline} {events : Array Event}
      {out : ByteArray} {r : State × Array Event × ByteArray},
      s.phase = .running pipe → pipe.WellFormed →
      runSteps s msgs events out = .ok r →
      ∃ (evs' : Array Event) (pipe' : Pipeline),
        r.2.1 = events ++ evs' ∧ r.1.phase = .running pipe' ∧
        pipe'.pending = shellRun pipe.pending evs' := by
  intro msgs
  induction msgs with
  | nil =>
    intro s pipe events out r hph hwf h
    cases h
    exact ⟨#[], pipe, Array.append_empty.symm, hph, rfl⟩
  | cons m rest ih =>
    intro s pipe events out r hph hwf h
    unfold runSteps at h
    cases hst : step s m with
    | error e =>
      rw [hst] at h
      cases h
    | ok res =>
      obtain ⟨s1, evs1, b1⟩ := res
      rw [hst] at h
      obtain ⟨pipe1, hph1, hfifo1⟩ := step_fifo hph hwf hst
      have hwf1 : pipe1.WellFormed :=
        pipe_wf_of_running hph1 (step_wellFormed (wf_of_phase_running hph hwf) hst)
      obtain ⟨evs2, pipe2, hev, hph2, hfifo2⟩ := ih hph1 hwf1 h
      refine ⟨evs1 ++ evs2, pipe2, ?_, hph2, ?_⟩
      · rw [hev, Array.append_assoc]
      · rw [hfifo2, hfifo1, shellRun_append]

/-- **FIFO refinement, whole frame batch**: the machine's pending-op queue
after stepping a list of frames is exactly the shell's FIFO after folding the
emitted events through `shellStep`. -/
theorem runSteps_fifo {msgs : List RawMessage} {s : State} {pipe : Pipeline}
    {s' : State} {evs : Array Event} {out : ByteArray}
    (hph : s.phase = .running pipe) (hwf : pipe.WellFormed)
    (h : runSteps s msgs #[] ByteArray.empty = .ok (s', evs, out)) :
    ∃ pipe', s'.phase = .running pipe' ∧ pipe'.pending = shellRun pipe.pending evs := by
  obtain ⟨evs', pipe', hev, hph', hfifo⟩ :=
    runSteps_fifo_aux (r := (s', evs, out)) hph hwf h
  have hevs : evs = evs' := by
    rw [Array.empty_append] at hev
    exact hev
  refine ⟨pipe', hph', ?_⟩
  rw [hevs]
  exact hfifo

/-- **FIFO refinement, whole TCP chunk**: everything the shell learns from one
`feed` moves its event-driven FIFO exactly as the machine moved its
pending-op queue. -/
theorem feed_fifo {s : State} {pipe : Pipeline} {chunk : ByteArray} {s' : State}
    {evs : Array Event} {out : ByteArray}
    (hph : s.phase = .running pipe) (hwf : pipe.WellFormed)
    (h : feed s chunk = .ok (s', evs, out)) :
    ∃ pipe', s'.phase = .running pipe' ∧ pipe'.pending = shellRun pipe.pending evs := by
  unfold feed at h
  split at h
  · cases h
  · split at h
    rename_i fed hd msgs decode htake
    exact runSteps_fifo (s := { s with decode := decode }) hph hwf h

/-- **Attribution**: a user-visible success is the terminal reply of the op at
the *head* of the correlation FIFO, and it removes exactly that one entry — so
every success is attributed to exactly one submitted operation, in submission
order. -/
theorem terminal_pops_head {s : State} {pipe : Pipeline} {msg : RawMessage}
    {s' : State} {ev : Event} {out : ByteArray} {k : OpKind} {rest : List OpKind}
    (hph : s.phase = .running pipe) (hwf : pipe.WellFormed)
    (hfifo : pipe.pending = k :: rest) (hterm : isTerminal k ev = true)
    (h : step s msg = .ok (s', #[ev], out)) :
    ∃ pipe', s'.phase = .running pipe' ∧ pipe'.pending = rest := by
  obtain ⟨pipe', hph', hp⟩ := step_fifo hph hwf h
  exact ⟨pipe', hph', by rw [hp, shellRun_single, hfifo, shellStep_pop hterm]⟩

/-- Complement: nothing else pops. A reply that is not the head op's terminal
and not an error leaves every pending request exactly where it was — in
particular a simple query's per-statement `commandComplete` does not complete
the query. -/
theorem nonterminal_preserves_fifo {s : State} {pipe : Pipeline} {msg : RawMessage}
    {s' : State} {ev : Event} {out : ByteArray} {k : OpKind} {rest : List OpKind}
    (hph : s.phase = .running pipe) (hwf : pipe.WellFormed)
    (hfifo : pipe.pending = k :: rest) (hterm : isTerminal k ev = false)
    (herr : isRecoverableError ev = false)
    (h : step s msg = .ok (s', #[ev], out)) :
    ∃ pipe', s'.phase = .running pipe' ∧ pipe'.pending = k :: rest := by
  obtain ⟨pipe', hph', hp⟩ := step_fifo hph hwf h
  exact ⟨pipe', hph', by rw [hp, shellRun_single, hfifo, shellStep_keep hterm herr]⟩

/-- An extended-protocol error cancels exactly the expectations up to the next
pipelined Sync — no more, no less. -/
theorem error_drops_to_sync {s : State} {pipe : Pipeline} {msg : RawMessage}
    {s' : State} {fields : ErrorFields} {out : ByteArray} {k : OpKind}
    {rest : List OpKind}
    (hph : s.phase = .running pipe) (hwf : pipe.WellFormed)
    (hfifo : pipe.pending = k :: rest) (hnotsync : k ≠ .sync)
    (hnotsimple : k ≠ .simpleQuery)
    (h : step s msg = .ok (s', #[.errorResponse fields], out)) :
    ∃ pipe', s'.phase = .running pipe' ∧ pipe'.pending = dropUntilSync rest := by
  obtain ⟨pipe', hph', hp⟩ := step_fifo hph hwf h
  refine ⟨pipe', hph', ?_⟩
  rw [hp, shellRun_single, hfifo,
    shellStep_abort (opKind_beq_eq_false hnotsync) (opKind_beq_eq_false hnotsimple)]

private theorem enqueue_pending {pipe : Pipeline} (hwf : pipe.WellFormed)
    (kind : OpKind) : (enqueue pipe kind).pending = pipe.pending ++ [kind] := by
  unfold enqueue
  split
  · next hc =>
    have hq : pipe.queued = #[] := hwf.2.1 hc
    show kind :: pipe.queued.toList = pipe.pending ++ [kind]
    rw [pending_nil hc hq, hq]
    rfl
  · next op hc =>
    rw [pending_cons (pipe := { pipe with queued := pipe.queued.push kind }) hc,
      pending_cons hc, Array.toList_push]
    rfl

private theorem submitIdle_fifo {s : State} {pipe : Pipeline} {req : Request}
    (hph : s.phase = .running pipe) (hwf : pipe.WellFormed) :
    ∀ {s' : State} {out : ByteArray}, submitIdle s pipe req = .ok (s', out) →
      (∃ pipe', s'.phase = .running pipe' ∧
        (pipe'.pending = pipe.pending ∨ ∃ k, pipe'.pending = pipe.pending ++ [k])) ∨
      s'.phase = .closed := by
  fun_cases submitIdle s pipe req with
  | case1 habt =>
    intro s' out h
    cases h
    obtain ⟨hc, hq⟩ := hwf.1 habt
    have hwf' : Pipeline.WellFormed { pipe with aborted := false } := by
      refine ⟨(fun hh => nomatch hh), (fun _ => hq), ?_⟩
      show (match pipe.current with
        | none => True
        | some op => op.Coherent ∧ _)
      rw [hc]
      exact True.intro
    exact Or.inl ⟨_, rfl, Or.inr ⟨.sync, enqueue_pending hwf' .sync⟩⟩
  | case2 habt =>
    intro s' out h
    cases h
    exact Or.inr rfl
  | case3 habt hne =>
    intro s' out h
    cases h
  | case12 hnab =>
    intro s' out h
    cases h
    exact Or.inl ⟨pipe, hph, Or.inl rfl⟩
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
    exact Or.inr rfl
  | _ =>
    intro s' out h
    cases h
    exact Or.inl ⟨_, rfl, Or.inr ⟨_, enqueue_pending hwf _⟩⟩

private theorem submitRunning_fifo {s : State} {pipe : Pipeline} {req : Request}
    (hph : s.phase = .running pipe) (hwf : pipe.WellFormed) :
    ∀ {s' : State} {out : ByteArray}, submitRunning s pipe req = .ok (s', out) →
      (∃ pipe', s'.phase = .running pipe' ∧
        (pipe'.pending = pipe.pending ∨ ∃ k, pipe'.pending = pipe.pending ++ [k])) ∨
      s'.phase = .closed := by
  fun_cases submitRunning s pipe req with
  | case1 op hcur info hprog data =>
    intro s' out h
    cases h
    exact Or.inl ⟨pipe, hph, Or.inl rfl⟩
  | case2 op hcur info hprog =>
    intro s' out h
    cases h
    exact Or.inl ⟨_, rfl, Or.inl (by rw [progressTo_pending, pending_cons hcur])⟩
  | case3 op hcur info hprog reason =>
    intro s' out h
    cases h
    exact Or.inl ⟨_, rfl, Or.inl (by rw [progressTo_pending, pending_cons hcur])⟩
  | case4 op hcur info hprog =>
    intro s' out h
    cases h
    exact Or.inl ⟨pipe, hph, Or.inl rfl⟩
  | case5 op hcur info hprog =>
    intro s' out h
    cases h
    exact Or.inr rfl
  | case6 op hcur info hprog hne =>
    intro s' out h
    cases h
  | case7 =>
    intro s' out h
    exact submitIdle_fifo hph hwf h
  | case8 =>
    intro s' out h
    exact submitIdle_fifo hph hwf h

/-- Submissions only ever **append** to the correlation FIFO: one entry per
accepted request, in submission order (Flush and COPY-data traffic add none;
Terminate closes the connection). With `feed_fifo` this is the FIFO
refinement in full — the shell's queue is always exactly the machine's. -/
theorem submit_fifo {s : State} {pipe : Pipeline} {req : Request} {s' : State}
    {out : ByteArray} (hph : s.phase = .running pipe) (hwf : pipe.WellFormed)
    (h : submit s req = .ok (s', out)) :
    (∃ pipe', s'.phase = .running pipe' ∧
      (pipe'.pending = pipe.pending ∨ ∃ k, pipe'.pending = pipe.pending ++ [k])) ∨
    s'.phase = .closed := by
  revert h
  fun_cases submit s req
  case case2 =>
    intro h
    cases h
    exact Or.inr rfl
  case case4 =>
    rename_i pipe2 hph2
    rw [hph] at hph2
    injection hph2 with hp
    subst hp
    intro h
    exact submitRunning_fifo hph hwf h
  all_goals (intro h; cases h)

end Machine
end Protocol
end Pg
