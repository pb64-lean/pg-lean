module

public import Pg.Config
public import TLS13.X509

public section

/-!
libpq-style root-certificate discovery and loading.

This module is the I/O boundary around tls13-lean's pure PEM and path
validation code. The connection layer supplies the configured `sslrootcert`
value and consumes the loaded anchors only in peer-verifying modes.
-/

namespace Pg
namespace Tls
namespace TrustStore

inductive Source where
  | configured
  | environment
  | default
  deriving Repr, BEq, DecidableEq

structure Selection where
  source : Source
  path : System.FilePath

structure Loaded where
  source : Source
  path : System.FilePath
  trustStore : TLS13.X509.Chain.TrustStore

/-- Only libpq's two peer-verifying modes may consult trust configuration. -/
def verificationRequested : SslMode → Bool
  | .verifyCa | .verifyFull => true
  | _ => false

/-- The trust-store gate is exactly the policy table's chain requirement:
`select`/`resolve`/`loadForVerification` load anchors for precisely the modes
`SslMode.policy` says must validate a chain. -/
theorem verificationRequested_eq_policy (mode : SslMode) :
    verificationRequested mode = (mode.policy).requireChain := by
  cases mode <;> rfl

private def checkedSelection (source : Source) (path : System.FilePath) :
    Except String Selection := do
  if path.toString.isEmpty then
    throw "TLS root certificate path must not be empty"
  if path.toString == "system" then
    throw "sslrootcert=system is not supported"
  pure { source, path }

/-- Pure source selection used by deterministic tests.

Precedence is an explicit connection value, `PGSSLROOTCERT`, then an existing
`$HOME/.postgresql/root.crt`. Non-verifying modes return `none` before
inspecting any supplied value. -/
def select
    (mode : SslMode)
    (configured environment home : Option System.FilePath)
    (defaultExists : Bool) : Except String (Option Selection) := do
  unless verificationRequested mode do
    return none
  match configured with
  | some path => some <$> checkedSelection .configured path
  | none =>
    match environment with
    | some path => some <$> checkedSelection .environment path
    | none =>
      let some home := home
        | throw "HOME is not set; specify sslrootcert for certificate verification"
      if home.toString.isEmpty then
        throw "HOME is empty; specify sslrootcert for certificate verification"
      let path := home / ".postgresql" / "root.crt"
      unless defaultExists do
        throw s!"TLS root certificate file does not exist: {path}"
      pure (some { source := .default, path })

/-- Trust anchors are never even looked up for a mode that does not require a
validated chain (`select` returns `none` before inspecting any input). -/
theorem select_none_of_not_requireChain {mode : SslMode}
    (h : (mode.policy).requireChain = false)
    (configured environment home : Option System.FilePath) (defaultExists : Bool) :
    select mode configured environment home defaultExists = .ok none := by
  unfold select
  rw [show verificationRequested mode = false from
    by rw [verificationRequested_eq_policy]; exact h]
  rfl

/-- Resolve the trust file without touching environment or filesystem state
for non-verifying modes. Explicit configuration also avoids consulting the
environment and home directory. -/
def resolve
    (mode : SslMode) (configured : Option System.FilePath := none) :
    IO (Option Selection) := do
  unless verificationRequested mode do
    return none
  match configured with
  | some path =>
    match checkedSelection .configured path with
    | .ok selection => pure (some selection)
    | .error error => throw (IO.userError error)
  | none =>
    match (← IO.getEnv "PGSSLROOTCERT") with
    | some value =>
      match checkedSelection .environment (value : System.FilePath) with
      | .ok selection => pure (some selection)
      | .error error => throw (IO.userError error)
    | none =>
      let some homeValue ← IO.getEnv "HOME"
        | throw (IO.userError
            "HOME is not set; specify sslrootcert for certificate verification")
      let home : System.FilePath := homeValue
      if home.toString.isEmpty then
        throw (IO.userError
          "HOME is empty; specify sslrootcert for certificate verification")
      let path := home / ".postgresql" / "root.crt"
      unless ← System.FilePath.pathExists path do
        throw (IO.userError s!"TLS root certificate file does not exist: {path}")
      pure (some { source := .default, path })

private def loadSelection (selection : Selection) : IO Loaded := do
  let text ←
    try IO.FS.readFile selection.path
    catch error =>
      throw (IO.userError
        s!"failed to read TLS root certificate file {selection.path}: {error}")
  let trustStore ←
    match TLS13.X509.Chain.TrustStore.decodePEM text with
    | .ok trustStore => pure trustStore
    | .error error =>
      throw (IO.userError
        s!"invalid TLS root certificate file {selection.path}: {error}")
  pure {
    source := selection.source
    path := selection.path
    trustStore
  }

/-- Resolve and parse a strict PEM trust bundle. `none` is returned only for
non-verifying modes; verification modes either load at least one anchor or
raise a path-qualified I/O/parse error. -/
def loadForVerification
    (mode : SslMode) (configured : Option System.FilePath := none) :
    IO (Option Loaded) := do
  let some selection ← resolve mode configured
    | return none
  some <$> loadSelection selection

end TrustStore
end Tls
end Pg
