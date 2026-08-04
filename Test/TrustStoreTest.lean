module

public import Pg

public section

namespace Pg
namespace Test

private def check (label : String) (condition : Bool) : IO Unit := do
  unless condition do
    throw (IO.userError s!"{label}: assertion failed")

private def path (value : String) : System.FilePath := value

private def expectSelection
    (label : String) (result : Except String (Option Tls.TrustStore.Selection))
    (source : Tls.TrustStore.Source) (expectedPath : String) : IO Unit :=
  match result with
  | .ok (some selection) => do
    check (label ++ " source") (selection.source == source)
    check (label ++ " path") (selection.path.toString == expectedPath)
  | .ok none =>
    throw (IO.userError s!"{label}: unexpectedly selected no trust file")
  | .error error =>
    throw (IO.userError s!"{label}: unexpected error: {error}")

private def expectSelectionError
    (label : String) (result : Except String (Option Tls.TrustStore.Selection)) :
    IO Unit :=
  match result with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError s!"{label}: invalid trust selection was accepted")

private def testPureSelection : IO Unit := do
  let configured := path "/configured/root.pem"
  let environment := path "/environment/root.pem"
  let home := path "/home/tester"

  expectSelection "configured precedence"
    (Tls.TrustStore.select .verifyCa
      (some configured) (some environment) (some home) true)
    .configured configured.toString
  expectSelection "environment precedence"
    (Tls.TrustStore.select .verifyFull
      none (some environment) (some home) true)
    .environment environment.toString
  expectSelection "default path"
    (Tls.TrustStore.select .verifyCa none none (some home) true)
    .default "/home/tester/.postgresql/root.crt"

  -- Bad values are intentionally not inspected outside verify modes.
  match Tls.TrustStore.select .require
      (some (path "")) (some (path "system")) none false with
  | .ok none => pure ()
  | _ => throw (IO.userError "sslmode=require consulted root certificate inputs")

  expectSelectionError "empty configured path"
    (Tls.TrustStore.select .verifyCa (some (path "")) none (some home) true)
  expectSelectionError "unsupported system roots"
    (Tls.TrustStore.select .verifyCa (some (path "system")) none (some home) true)
  expectSelectionError "missing default root"
    (Tls.TrustStore.select .verifyCa none none (some home) false)
  expectSelectionError "missing HOME"
    (Tls.TrustStore.select .verifyCa none none none false)

private def testFileLoading : IO Unit := do
  let fixture := path "Test/Fixtures/TlsCertificateVerify/rsa.pem"
  let some loaded ← Tls.TrustStore.loadForVerification .verifyCa (some fixture)
    | throw (IO.userError "verify-ca did not load configured trust file")
  check "loaded configured source" (loaded.source == .configured)
  check "loaded configured path" (loaded.path.toString == fixture.toString)
  check "loaded anchor count" (loaded.trustStore.anchors.size == 1)

  -- A nonexistent configured path proves the early mode guard performs no
  -- trust-file I/O for require.
  let skipped ← Tls.TrustStore.loadForVerification .require
    (some (path "definitely-does-not-exist.pem"))
  check "require skips configured root file" skipped.isNone

/-- The parts of the TLS decision table the laws deliberately leave open:
which transport each opportunistic mode starts with and retries with. The
safety properties themselves (chain ⇒ encryption, hostname ⇒ chain, no
insecure fallback) are kernel-checked in `Pg/Config.lean`. -/
private def testTlsPolicyTable : IO Unit := do
  check "disable starts plaintext" (SslMode.disable.initialAttempt == .plaintext)
  check "allow starts plaintext" (SslMode.allow.initialAttempt == .plaintext)
  check "prefer starts optional TLS"
    (SslMode.prefer.initialAttempt == .negotiateTls false)
  check "require starts required TLS"
    (SslMode.require.initialAttempt == .negotiateTls true)
  check "verify-full starts required TLS"
    (SslMode.verifyFull.initialAttempt == .negotiateTls true)
  check "allow retries with required TLS"
    (SslMode.allow.fallbackAttempt == some (.negotiateTls true))
  check "prefer retries in plaintext"
    (SslMode.prefer.fallbackAttempt == some .plaintext)
  check "require never retries" (SslMode.require.fallbackAttempt == none)
  check "verify-ca never retries" (SslMode.verifyCa.fallbackAttempt == none)
  check "verify-full never retries" (SslMode.verifyFull.fallbackAttempt == none)
  check "verify-full checks the hostname"
    (SslMode.verifyFull.policy).requireHostname
  check "verify-ca does not check the hostname"
    (!(SslMode.verifyCa.policy).requireHostname)
  check "require validates no chain" (!(SslMode.require.policy).requireChain)

def run : IO Unit := do
  testPureSelection
  testFileLoading
  testTlsPolicyTable
  IO.println "all TLS trust-store assertions passed"

end Test
end Pg

def main : IO Unit :=
  Pg.Test.run
