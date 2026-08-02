import Pg.Protocol.Machine
import Test.Support.Hex
import Test.Support.Backend
import Test.Support.Script

/-!
Unit-level machine assertions: the submit-gating table, the error taxonomy's
fatal/recoverable/rejection split, `dropAborted`, and phase-edge protocol
violations. Flow-level behavior lives in FlowTest.
-/

open Pg.Protocol
open Pg.Protocol.Machine
open Pg.TestSupport
open Pg.TestSupport.Be

def expect (cond : Bool) (msg : String) : IO Unit := do
  unless cond do throw (IO.userError msg)

def expectSubmitError (s : State) (req : Request) (want : ErrorMatch) (label : String) :
    IO Unit := do
  match Machine.submit s req with
  | .ok _ => throw (IO.userError s!"{label}: expected rejection, got ok")
  | .error e =>
    unless want.accepts e do
      throw (IO.userError s!"{label}: expected {repr want}, got {repr e}")

def expectStepError (s : State) (bytes : ByteArray) (want : ErrorMatch) (label : String) :
    IO Unit := do
  match Machine.feed s bytes with
  | .ok (_, evs, _) => throw (IO.userError s!"{label}: expected fatal, got events {repr evs}")
  | .error e =>
    unless want.accepts e do
      throw (IO.userError s!"{label}: expected {repr want}, got {repr e}")

def okFeed (s : State) (bytes : ByteArray) (label : String) : IO State := do
  match Machine.feed s bytes with
  | .ok (s', _, _) => pure s'
  | .error e => throw (IO.userError s!"{label}: {repr e}")

def okSubmit (s : State) (req : Request) (label : String) : IO State := do
  match Machine.submit s req with
  | .ok (s', _) => pure s'
  | .error e => throw (IO.userError s!"{label}: {repr e}")

def expectScramSelection (cfg : Config) (mechanisms : Array String)
    (mechanism first : String) (label : String) : IO State := do
  let (s, _) := Machine.start cfg
  match Machine.feed s (authSasl mechanisms) with
  | .error e => throw (IO.userError s!"{label}: unexpected {repr e}")
  | .ok (s, events, bytes) =>
    expect events.isEmpty s!"{label}: unexpected events"
    expect (bytes == Frontend.saslInitialResponse mechanism first.toUTF8)
      s!"{label}: wrong SASL initial response"
    expect (s.negotiatedSaslMechanism? == some mechanism)
      s!"{label}: selected mechanism not retained"
    pure s

def expectChannelBindingError (cfg : Config) (request : ByteArray)
    (failure : Pg.ChannelBindingFailure) (label : String) : IO Unit := do
  let (s, _) := Machine.start cfg
  match Machine.feed s request with
  | .error (.channelBinding actual) =>
    expect (actual == failure) s!"{label}: expected {repr failure}, got {repr actual}"
  | .error e => throw (IO.userError s!"{label}: expected channel binding error, got {repr e}")
  | .ok _ => throw (IO.userError s!"{label}: expected channel binding error, got ok")

/-- A trust-authenticated ready connection. -/
def connected : IO State := do
  let (s, _) := Machine.start testConfig
  okFeed s (authOk ++ backendKeyData 7 (hex "00 00 00 2a") ++
    parameterStatus "server_version" "17.5" ++ readyForQuery 'I') "connect"

def main : IO Unit := do
  -- startup gating: only terminate is allowed
  let (s0, _) := Machine.start testConfig
  expectSubmitError s0 (.simpleQuery "SELECT 1") .rejectedInvalid "query during startup"
  expectSubmitError s0 .sync .rejectedInvalid "sync during startup"
  let closed ← okSubmit s0 .terminate "terminate during startup"
  expectSubmitError closed (.simpleQuery "x") .rejectedInvalid "query after terminate"
  expectStepError closed authOk .protocol "message after terminate"

  -- connected state accessors
  let s ← connected
  expect s.isQuiescent "quiescent after connect"
  expect (s.parameter? "server_version" == some "17.5") "parameter tracking"
  expect (s.cancelKey? == some { processId := 7, secret := hex "00 00 00 2a" }) "cancel key"
  expect (s.txStatus == .idle) "tx status"

  -- copy gating: no COPY in progress
  expectSubmitError s (.copyData (ascii "x")) .rejectedInvalid "copyData without COPY"
  expectSubmitError s .copyDone .rejectedInvalid "copyDone without COPY"
  expectSubmitError s (.copyFail "x") .rejectedInvalid "copyFail without COPY"

  -- extended error with NO sync queued (Flush-driven): pipeline aborts,
  -- submits gate on rejectedAborted until the user syncs
  let s1 ← okSubmit s (.parse "st" "SELECT broken") "parse"
  let s1 ← okSubmit s1 .flush "flush"
  let s1 ← okFeed s1 (errorResponse "ERROR" "42601" "syntax error") "parse error"
  expectSubmitError s1 (.parse "st2" "SELECT 1") .rejectedAborted "parse while aborted"
  expectSubmitError s1 (.execute "") .rejectedAborted "execute while aborted"
  expectSubmitError s1 (.simpleQuery "SELECT 1") .rejectedAborted "simple query while aborted"
  let s1 ← okSubmit s1 .sync "sync clears abort"
  let s1 ← okFeed s1 (readyForQuery 'I') "ready after sync"
  expect s1.isQuiescent "quiescent after abort recovery"

  -- extended error WITH a sync already queued: drop-to-sync, no abort gate
  let s2 ← okSubmit s (.parse "st" "SELECT broken") "parse2"
  let s2 ← okSubmit s2 (.bind "" "st") "bind2"
  let s2 ← okSubmit s2 (.execute "") "execute2"
  let s2 ← okSubmit s2 .sync "sync2"
  let s2 ← okFeed s2 (errorResponse "ERROR" "42601" "syntax error") "error2"
  -- recovery armed: new submits queue normally behind the draining sync
  let s2 ← okSubmit s2 (.parse "st3" "SELECT 1") "parse behind drain"
  let s2 ← okFeed s2 (readyForQuery 'I') "sync ready"
  let s2 ← okFeed s2 parseComplete "queued parse completes"
  expect s2.isQuiescent "quiescent after drop-to-sync"

  -- dropAborted directly
  let (rest, found) := dropAborted (· == OpKind.sync)
    #[OpKind.bind, OpKind.execute, OpKind.sync, OpKind.parse]
  expect (found && rest == #[OpKind.sync, OpKind.parse]) "dropAborted finds sync"
  let (rest2, found2) := dropAborted (· == OpKind.sync) #[OpKind.bind, OpKind.execute]
  expect (!found2 && rest2 == #[]) "dropAborted without sync"

  -- fatal taxonomy
  expectStepError s (errorResponse "FATAL" "57P01" "shutting down") .serverFatal
    "unsolicited error while quiescent"
  let (f0, _) := Machine.start testConfig
  expectStepError f0 (errorResponse "FATAL" "28P01" "password authentication failed")
    .serverFatal "auth rejection"
  expectStepError f0 authKerberos .unsupportedAuth "kerberos"
  expectStepError f0 (authSasl #["SCRAM-SHA-256-PLUS"]) .channelBinding
    "PLUS advertised without TLS"
  let (noPw, _) := Machine.start { testConfig with password := none }
  expectStepError noPw authCleartext .missingPassword "missing password"
  expectStepError f0 (backendKeyData 1 (hex "00 00 00 01")) .protocol "key before authOk"
  expectStepError f0 (readyForQuery 'I') .protocol "ready before authOk"
  expectStepError f0 (hex "5a 00 00 00 05 58") .decode "corrupt ready payload"
  expectStepError s (rowDescription #[col "a" 23]) .protocol "unsolicited RowDescription"
  expectStepError s parseComplete .protocol "unsolicited ParseComplete"

  -- SCRAM channel-binding mechanism selection. TLS state is represented by
  -- this connection's leaf-certificate hash, never by policy alone.
  let binding := hex
    "00 01 02 03 04 05 06 07 08 09 0a 0b 0c 0d 0e 0f \
     10 11 12 13 14 15 16 17 18 19 1a 1b 1c 1d 1e 1f"
  let tlsPrefer := {
    testConfig with
    channelBinding := .prefer
    tlsServerEndPoint := some binding
  }
  let plusFirst :=
    "p=tls-server-end-point,,n=user,r=rOprNGfwEbeRWgbNEkqO"
  let _ ← expectScramSelection tlsPrefer
    #["SCRAM-SHA-256", "SCRAM-SHA-256-PLUS"]
    "SCRAM-SHA-256-PLUS" plusFirst "prefer PLUS base-first"
  let _ ← expectScramSelection tlsPrefer
    #["SCRAM-SHA-256-PLUS", "SCRAM-SHA-256"]
    "SCRAM-SHA-256-PLUS" plusFirst "prefer PLUS plus-first"
  let _ ← expectScramSelection tlsPrefer #["SCRAM-SHA-256"]
    "SCRAM-SHA-256" "y,,n=user,r=rOprNGfwEbeRWgbNEkqO"
    "TLS prefer downgrade signal"
  let _ ← expectScramSelection testConfig #["SCRAM-SHA-256"]
    "SCRAM-SHA-256" "n,,n=user,r=rOprNGfwEbeRWgbNEkqO"
    "plaintext prefer"
  let tlsDisable := { tlsPrefer with channelBinding := .disable }
  let _ ← expectScramSelection tlsDisable
    #["SCRAM-SHA-256-PLUS", "SCRAM-SHA-256"]
    "SCRAM-SHA-256" "n,,n=user,r=rOprNGfwEbeRWgbNEkqO"
    "TLS disabled binding"
  let tlsRequire := { tlsPrefer with channelBinding := .require }
  let _ ← expectScramSelection tlsRequire #["SCRAM-SHA-256-PLUS"]
    "SCRAM-SHA-256-PLUS" plusFirst "TLS required PLUS"
  expectChannelBindingError tlsRequire (authSasl #["SCRAM-SHA-256"])
    .plusNotOffered "require missing PLUS"
  expectChannelBindingError { testConfig with channelBinding := .require }
    (authSasl #["SCRAM-SHA-256", "SCRAM-SHA-256-PLUS"])
    .tlsRequired "require without TLS"

  -- `require` must reject every non-SASL path before releasing a password or
  -- accepting trust authentication without a completed PLUS exchange.
  expectChannelBindingError tlsRequire authOk .plusNotOffered
    "require rejects trust"
  expectChannelBindingError tlsRequire authCleartext .plusNotOffered
    "require rejects cleartext"
  expectChannelBindingError tlsRequire (authMd5 (hex "01 02 03 04"))
    .plusNotOffered "require rejects MD5"

  -- protocol 3.0 requires a 4-byte cancel key
  let (k0, _) := Machine.start testConfig
  expectStepError k0 (authOk ++ backendKeyData 7 (hex "00 01 02 03 04 05 06 07"))
    .protocol "8-byte key under 3.0"

  -- 3.2: negotiate down to 3.0, then a 4-byte key is required and accepted
  let (n0, _) := Machine.start { testConfig with requestedVersion := .v3_2 }
  let n1 ← okFeed n0 (negotiateProtocolVersion 0 #[]) "negotiate down"
  expect (n1.protocolVersion == .v3_0) "negotiated version recorded"
  let n2 ← okFeed n1 (authOk ++ backendKeyData 7 (hex "00 00 00 01") ++ readyForQuery 'I')
    "ready after negotiation"
  expect n2.isQuiescent "quiescent after negotiated connect"
  -- 3.2 kept: variable-length key accepted
  let (v0, _) := Machine.start { testConfig with requestedVersion := .v3_2 }
  let key := hex (String.join (List.replicate 8 "aa bb cc dd "))
  let v1 ← okFeed v0 (authOk ++ backendKeyData 9 key ++ readyForQuery 'I') "3.2 connect"
  expect (v1.cancelKey? == some { processId := 9, secret := key }) "3.2 long key stored"

  IO.println "all machine assertions passed"
