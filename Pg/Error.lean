module

public import Pg.Protocol.Backend
public import Pg.Protocol.Machine
public import TLS13.X509

public section

namespace Pg

/-- Client-facing error split along the machine's taxonomy: `server` and
`rejected` leave the connection usable; `fatal` and `disconnected` mean it is
gone. -/
inductive Error where
  /-- Statement-level server error (full §53.8 fields, SQLSTATE included). -/
  | server (fields : Protocol.ErrorFields)
  /-- Submit rejection: caller bug or aborted pipeline; state unchanged. -/
  | rejected (e : Protocol.Machine.PgError)
  /-- Connection-poisoning failure: protocol violation, auth failure, fatal
  server error. Close and reconnect. -/
  | fatal (e : Protocol.Machine.PgError)
  /-- The socket reached EOF mid-conversation. -/
  | disconnected
  /-- A TLS peer certificate could not be chained to the configured trust
  store or failed an X.509 path constraint. -/
  | tlsChainVerification (failure : TLS13.X509.Chain.Failure)
  /-- The verified TLS leaf certificate did not identify the connection
  host. -/
  | tlsHostnameVerification (failure : TLS13.X509.Hostname.Failure)
  /-- The requested SCRAM channel-binding policy could not be satisfied. -/
  | channelBinding (failure : ChannelBindingFailure)
  deriving Repr, Inhabited

namespace Error

def sqlState? : Error → Option String
  | .server fields => fields.sqlState?
  | .fatal (.serverFatal fields) => fields.sqlState?
  | _ => none

private def chainFailureCategory : TLS13.X509.Chain.Failure → String
  | .unknownIssuer _ => "unknown issuer"
  | .notYetValid .. => "not yet valid"
  | .expired .. => "expired"
  | .badSignature .. => "bad signature"
  | .notCA _ => "issuer is not a CA"
  | .keyCertSignMissing _ => "issuer cannot sign certificates"
  | .pathLenExceeded .. => "path length exceeded"
  | .unhandledCriticalExtension .. => "unhandled critical extension"
  | .loop _ => "certificate path loop"
  | .maximumDepthExceeded _ => "certificate path too deep"
  | .maximumIssuerAttemptsExceeded _ => "certificate path search limit"

def toMessage : Error → String
  | .server fields =>
    let code := fields.sqlState?.getD "?????"
    let msg := fields.message?.getD "unknown error"
    s!"server error {code}: {msg}"
  | .rejected e => s!"request rejected: {repr e}"
  | .fatal (.serverFatal fields) =>
    let code := fields.sqlState?.getD "?????"
    let msg := fields.message?.getD "unknown error"
    s!"fatal server error {code}: {msg}"
  | .fatal e => s!"connection error: {repr e}"
  | .disconnected => "server closed the connection"
  | .tlsChainVerification failure =>
    s!"TLS certificate verification failed ({chainFailureCategory failure}): {failure}"
  | .tlsHostnameVerification failure =>
    s!"TLS hostname verification failed: {failure}"
  | .channelBinding failure =>
    s!"SCRAM channel binding failed: {failure}"

end Error

instance : ToString Error := ⟨Error.toMessage⟩

end Pg
