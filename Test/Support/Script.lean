module

public import Pg.Protocol.Machine
public import Test.Support.Hex

public section

namespace Pg
namespace TestSupport

open Pg.Protocol

/-!
Scripted-exchange runner for hermetic protocol-flow tests: a `Script` is an
authored client/server exchange executed against the pure `Machine`, with
strict expectations on emitted events, written bytes, rejections, and fatal
errors. `runScriptTortured` re-runs every script with the backend bytes
delivered whole and in 1/3/7-byte chunks — semantically identical by
construction, so any divergence is a framing bug.
-/

/-- RFC 7677's user/password plus its client nonce: with these, the entire
SCRAM exchange is byte-deterministic and the RFC's example messages apply
verbatim. -/
def testConfig : Machine.Config :=
  { user := "user"
    password := some "pencil"
    scramNonce := "rOprNGfwEbeRWgbNEkqO" }

inductive ErrorMatch where
  | any
  | decode
  | protocol
  | serverFatal
  | authFailed
  | unsupportedAuth
  | missingPassword
  | channelBinding
  | rejectedInvalid
  | rejectedAborted
  deriving Repr, Inhabited

def ErrorMatch.accepts : ErrorMatch → Machine.PgError → Bool
  | .any, _ => true
  | .decode, .decode _ => true
  | .protocol, .protocol _ => true
  | .serverFatal, .serverFatal _ => true
  | .authFailed, .authFailed _ => true
  | .unsupportedAuth, .unsupportedAuth _ => true
  | .missingPassword, .missingPassword => true
  | .channelBinding, .channelBinding _ => true
  | .rejectedInvalid, .rejectedInvalid _ => true
  | .rejectedAborted, .rejectedAborted => true
  | _, _ => false

inductive Step where
  /-- Submit must succeed; its bytes are discarded (request encodings are
  golden-pinned in WireTest — use `sendExpect` to assert them in a flow). -/
  | send (req : Machine.Request)
  /-- Submit must succeed and produce exactly these bytes (not accumulated). -/
  | sendExpect (req : Machine.Request) (bytes : ByteArray)
  /-- Submit must fail with a matching rejection; state is unchanged by the
  `submit` contract. -/
  | reject (req : Machine.Request) (err : ErrorMatch := .any)
  /-- Backend bytes through `Machine.feed` (chunked per runner config). -/
  | recv (bytes : ByteArray)
  /-- Drain the accumulated events; must equal exactly. -/
  | expectEvents (events : Array Machine.Event)
  /-- Drain the accumulated writes; must equal exactly. -/
  | expectWrite (bytes : ByteArray)
  | expectNoOutput
  /-- Feeding these bytes must poison the machine; must be the last step. -/
  | expectFatal (bytes : ByteArray) (err : ErrorMatch := .any)
  | check (label : String) (predicate : Machine.State → Bool)

abbrev Script := Array Step

private def describeStep : Step → String
  | .send req => s!"send {repr req}"
  | .sendExpect req _ => s!"sendExpect {repr req}"
  | .reject req _ => s!"reject {repr req}"
  | .recv bytes => s!"recv {hexDump (bytes.extract 0 8)}…"
  | .expectEvents _ => "expectEvents"
  | .expectWrite _ => "expectWrite"
  | .expectNoOutput => "expectNoOutput"
  | .expectFatal .. => "expectFatal"
  | .check label _ => s!"check {label}"

inductive Chunking where
  | whole
  | bytes (n : Nat)
  deriving Repr

private def Chunking.describe : Chunking → String
  | .whole => "whole"
  | .bytes n => s!"{n}-byte chunks"

structure RunnerCfg where
  cfg : Machine.Config := testConfig
  chunking : Chunking := .whole

private def feedChunked (m : Machine.State) (bytes : ByteArray) (chunking : Chunking) :
    Except Machine.PgError (Machine.State × Array Machine.Event × ByteArray) := do
  match chunking with
  | .whole => Machine.feed m bytes
  | .bytes n =>
    let n := max n 1
    let mut cur := m
    let mut events : Array Machine.Event := #[]
    let mut out := ByteArray.empty
    let mut i := 0
    while i < bytes.size do
      let stop := min (i + n) bytes.size
      let (s', evs, o) ← Machine.feed cur (bytes.extract i stop)
      cur := s'
      events := events ++ evs
      out := out ++ o
      i := stop
    pure (cur, events, out)

private def firstDiff [BEq α] (a b : Array α) : Nat := Id.run do
  for i in [0:max a.size b.size] do
    if a[i]? != b[i]? then return i
  return a.size

def runScript (script : Script) (rcfg : RunnerCfg := {}) : Except String Unit := do
  let (m0, startBytes) := Machine.start rcfg.cfg
  let mut m := m0
  let mut events : Array Machine.Event := #[]
  let mut writes := startBytes
  let mut dead := false
  let mut i := 0
  let fail : Nat → Step → String → Except String Unit := fun i step msg =>
    throw s!"step {i} ({describeStep step}) [{rcfg.chunking.describe}]: {msg}"
  for step in script do
    if dead then
      fail i step "machine already poisoned (expectFatal must be last)"
    match step with
    | .send req =>
      match Machine.submit m req with
      | .ok (m', _) => m := m'
      | .error e => fail i step s!"submit failed: {repr e}"
    | .sendExpect req want =>
      match Machine.submit m req with
      | .ok (m', bytes) =>
        m := m'
        unless bytes == want do
          fail i step s!"wrote\n  got  {hexDump bytes}\n  want {hexDump want}"
      | .error e => fail i step s!"submit failed: {repr e}"
    | .reject req errMatch =>
      match Machine.submit m req with
      | .ok _ => fail i step "expected rejection, submit succeeded"
      | .error e =>
        unless errMatch.accepts e do
          fail i step s!"expected {repr errMatch}, got {repr e}"
    | .recv bytes =>
      match feedChunked m bytes rcfg.chunking with
      | .ok (m', evs, out) =>
        m := m'
        events := events ++ evs
        writes := writes ++ out
      | .error e => fail i step s!"feed failed: {repr e}"
    | .expectEvents want =>
      unless events == want do
        let d := firstDiff events want
        fail i step s!"event {d}:\n  got  {repr events[d]?}\n  want {repr want[d]?}\n  (all got: {repr events})"
      events := #[]
    | .expectWrite want =>
      unless writes == want do
        fail i step s!"writes:\n  got  {hexDump writes}\n  want {hexDump want}"
      writes := ByteArray.empty
    | .expectNoOutput =>
      unless events.isEmpty do fail i step s!"unexpected events: {repr events}"
      unless writes.isEmpty do fail i step s!"unexpected writes: {hexDump writes}"
    | .expectFatal bytes errMatch =>
      match feedChunked m bytes rcfg.chunking with
      | .ok (_, evs, _) => fail i step s!"expected fatal error, got events {repr evs}"
      | .error e =>
        unless errMatch.accepts e do
          fail i step s!"expected {repr errMatch}, got {repr e}"
        dead := true
    | .check label predicate =>
      unless predicate m do fail i step s!"predicate {label} is false"
    i := i + 1
  unless dead do
    unless events.isEmpty do
      throw s!"end of script: unconsumed events {repr events}"
    unless writes.isEmpty do
      throw s!"end of script: unconsumed writes {hexDump writes}"

/-- Run whole plus 1/3/7-byte fragmentation; all four must pass. -/
def runScriptTortured (script : Script) (rcfg : RunnerCfg := {}) : Except String Unit := do
  runScript script rcfg
  for n in [1, 3, 7] do
    runScript script { rcfg with chunking := .bytes n }

def runIO (name : String) (script : Script) (rcfg : RunnerCfg := {}) : IO Unit := do
  match runScriptTortured script rcfg with
  | .ok () => pure ()
  | .error e => throw (IO.userError s!"{name}: {e}")

end TestSupport
end Pg
