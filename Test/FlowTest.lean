import Pg.Protocol.Machine
import Test.Support.Hex
import Test.Support.Backend
import Test.Support.Script

/-!
Scripted full-exchange flows (startup/auth/simple query), each run whole and
under 1/3/7-byte fragmentation. The SCRAM script reproduces RFC 7677's example
exchange byte for byte (testConfig pins user/password/nonce to the RFC's).
-/

open Pg.Protocol
open Pg.Protocol.Machine
open Pg.TestSupport
open Pg.TestSupport.Be

def startupGolden : ByteArray :=
  encodeStartup #[("user", "user"), ("client_encoding", "UTF8")]

/-- Shared prologue: trust auth with key data and a server parameter. -/
def connectTrust : Script := #[
  .expectWrite startupGolden,
  .recv (authOk ++ backendKeyData 7 (hex "00 00 00 2a") ++
    parameterStatus "server_version" "17.5" ++ readyForQuery 'I'),
  .expectEvents #[.authOk, .parameterStatus "server_version" "17.5", .ready .idle],
  .check "cancel key stored" (·.cancelKey?.isSome),
  .check "quiescent" (·.isQuiescent)]

def rfcServerFirst : String :=
  "r=rOprNGfwEbeRWgbNEkqO%hvYDpWUa2RaTCAfuxFIlj)hNlF$k0,s=W22ZaJ0SNY7soEsUEjb6gQ==,i=4096"

def rfcClientFinal : String :=
  "c=biws,r=rOprNGfwEbeRWgbNEkqO%hvYDpWUa2RaTCAfuxFIlj)hNlF$k0,p=dHzbZapWIk4jUhN+Ute9ytag9zjfMHgsqmmiz7AndVQ="

def rfcServerFinal : String := "v=6rriTRBi23WpRR/wtup+mMhUZUn/dB5nLTJRsjl95G4="

def plusBinding : ByteArray :=
  hex "00 01 02 03 04 05 06 07 08 09 0a 0b 0c 0d 0e 0f \
       10 11 12 13 14 15 16 17 18 19 1a 1b 1c 1d 1e 1f"

def plusClientFinal : String :=
  "c=cD10bHMtc2VydmVyLWVuZC1wb2ludCwsAAECAwQFBgcICQoLDA0ODxAREhMUFRYXGBkaGxwdHh8=" ++
  ",r=rOprNGfwEbeRWgbNEkqO%hvYDpWUa2RaTCAfuxFIlj)hNlF$k0" ++
  ",p=nY1Wus9a+gM2DrbQ1msXFgyhW6KM5ktOxWiU+/P/EGY="

def plusServerFinal : String :=
  "v=RwppMGddhz/J0lFYaRReBjXcQeNUFP5Qc76Lo5Exrig="

def supportedNotUsedClientFinal : String :=
  "c=eSws,r=rOprNGfwEbeRWgbNEkqO%hvYDpWUa2RaTCAfuxFIlj)hNlF$k0" ++
  ",p=FoqiHTtQEDE8lz1CdaEe3tK4mS+iMDTl77SPyDS53DY="

def supportedNotUsedServerFinal : String :=
  "v=dI4KpiQJwBr1+V+K6U1dA6l6I4I9DUNXWND4pcpRU3U="

def main : IO Unit := do
  runIO "trust connect" connectTrust

  runIO "cleartext auth" #[
    .expectWrite startupGolden,
    .recv authCleartext,
    .expectWrite (Frontend.password "pencil"),
    .recv (authOk ++ readyForQuery 'I'),
    .expectEvents #[.authOk, .ready .idle]]

  runIO "md5 auth" #[
    .expectWrite startupGolden,
    .recv (authMd5 (hex "01 02 03 04")),
    .expectWrite (Frontend.password
      (Pg.Crypto.md5PasswordHash "user" "pencil" (hex "01 02 03 04"))),
    .recv (authOk ++ readyForQuery 'I'),
    .expectEvents #[.authOk, .ready .idle]]

  runIO "scram auth (RFC 7677 bytes)" #[
    .expectWrite startupGolden,
    .recv (authSasl #["SCRAM-SHA-256"]),
    .expectWrite (Frontend.saslInitialResponse "SCRAM-SHA-256"
      (ascii "n,,n=user,r=rOprNGfwEbeRWgbNEkqO")),
    .recv (authSaslContinue rfcServerFirst),
    .expectWrite (Frontend.saslResponse (ascii rfcClientFinal)),
    .recv (authSaslFinal rfcServerFinal),
    .expectNoOutput,
    .recv (authOk ++ backendKeyData 1234 (hex "00 00 16 2e") ++ readyForQuery 'I'),
    .expectEvents #[.authOk, .ready .idle],
    .check "key stored" (·.cancelKey?.isSome)]

  -- The connection machine must carry the selected leaf binding through the
  -- full PLUS exchange, not merely choose the right mechanism name.
  runIO "scram PLUS auth (bound RFC 7677 bytes)" #[
    .expectWrite startupGolden,
    .recv (authSasl #["SCRAM-SHA-256", "SCRAM-SHA-256-PLUS"]),
    .expectWrite (Frontend.saslInitialResponse "SCRAM-SHA-256-PLUS"
      (ascii "p=tls-server-end-point,,n=user,r=rOprNGfwEbeRWgbNEkqO")),
    .check "PLUS mechanism retained"
      (·.negotiatedSaslMechanism? == some "SCRAM-SHA-256-PLUS"),
    .recv (authSaslContinue rfcServerFirst),
    .expectWrite (Frontend.saslResponse (ascii plusClientFinal)),
    .recv (authSaslFinal plusServerFinal),
    .expectNoOutput,
    .recv (authOk ++ readyForQuery 'I'),
    .expectEvents #[.authOk, .ready .idle]
  ] { cfg := { testConfig with tlsServerEndPoint := some plusBinding } }

  -- If TLS exists but the server omits PLUS, `prefer` uses base SCRAM with
  -- GS2 `y`; its exact `c=eSws` value participates in both proof signatures.
  runIO "scram TLS downgrade signal (bound RFC 7677 bytes)" #[
    .expectWrite startupGolden,
    .recv (authSasl #["SCRAM-SHA-256"]),
    .expectWrite (Frontend.saslInitialResponse "SCRAM-SHA-256"
      (ascii "y,,n=user,r=rOprNGfwEbeRWgbNEkqO")),
    .check "base mechanism retained after y"
      (·.negotiatedSaslMechanism? == some "SCRAM-SHA-256"),
    .recv (authSaslContinue rfcServerFirst),
    .expectWrite (Frontend.saslResponse (ascii supportedNotUsedClientFinal)),
    .recv (authSaslFinal supportedNotUsedServerFinal),
    .expectNoOutput,
    .recv (authOk ++ readyForQuery 'I'),
    .expectEvents #[.authOk, .ready .idle]
  ] { cfg := { testConfig with tlsServerEndPoint := some plusBinding } }

  runIO "scram forged server signature" #[
    .expectWrite startupGolden,
    .recv (authSasl #["SCRAM-SHA-256"]),
    .expectWrite (Frontend.saslInitialResponse "SCRAM-SHA-256"
      (ascii "n,,n=user,r=rOprNGfwEbeRWgbNEkqO")),
    .recv (authSaslContinue rfcServerFirst),
    .expectWrite (Frontend.saslResponse (ascii rfcClientFinal)),
    .expectFatal (authSaslFinal "v=AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA=")
      .authFailed]

  runIO "scram server skips final" #[
    .expectWrite startupGolden,
    .recv (authSasl #["SCRAM-SHA-256"]),
    .expectWrite (Frontend.saslInitialResponse "SCRAM-SHA-256"
      (ascii "n,,n=user,r=rOprNGfwEbeRWgbNEkqO")),
    .recv (authSaslContinue rfcServerFirst),
    .expectWrite (Frontend.saslResponse (ascii rfcClientFinal)),
    .expectFatal authOk .authFailed]

  runIO "server rejects password" #[
    .expectWrite startupGolden,
    .expectFatal (errorResponse "FATAL" "28P01" "password authentication failed for user")
      .serverFatal]

  runIO "simple query, one row" (connectTrust ++ #[
    .sendExpect (.simpleQuery "SELECT 1") (encodeQuery "SELECT 1"),
    .recv (rowDescription #[col "?column?" 23] ++ row #["1"] ++
      commandComplete "SELECT 1" ++ readyForQuery 'I'),
    .expectEvents #[
      .rowDescription #[col "?column?" 23],
      .dataRow #[some (ascii "1")],
      .commandComplete "SELECT 1",
      .ready .idle],
    .check "quiescent" (·.isQuiescent)])

  runIO "simple query, zero rows" (connectTrust ++ #[
    .send (.simpleQuery "SELECT 1 WHERE false"),
    .recv (rowDescription #[col "?column?" 23] ++ commandComplete "SELECT 0" ++
      readyForQuery 'I'),
    .expectEvents #[
      .rowDescription #[col "?column?" 23],
      .commandComplete "SELECT 0",
      .ready .idle]])

  runIO "simple query, multi-statement" (connectTrust ++ #[
    .send (.simpleQuery "SELECT 1; UPDATE t SET x = 1; SELECT 2"),
    .recv (rowDescription #[col "?column?" 23] ++ row #["1"] ++
      commandComplete "SELECT 1" ++ commandComplete "UPDATE 3" ++
      rowDescription #[col "?column?" 23] ++ row #["2"] ++
      commandComplete "SELECT 1" ++ readyForQuery 'T'),
    .expectEvents #[
      .rowDescription #[col "?column?" 23],
      .dataRow #[some (ascii "1")],
      .commandComplete "SELECT 1",
      .commandComplete "UPDATE 3",
      .rowDescription #[col "?column?" 23],
      .dataRow #[some (ascii "2")],
      .commandComplete "SELECT 1",
      .ready .inTransaction],
    .check "tx open" (·.txStatus == .inTransaction)])

  runIO "simple query, error mid-results" (connectTrust ++ #[
    .send (.simpleQuery "SELECT * FROM big"),
    .recv (rowDescription #[col "x" 23] ++ row #["1"] ++
      errorResponse "ERROR" "57014" "canceling statement" ++ readyForQuery 'I'),
    .expectEvents #[
      .rowDescription #[col "x" 23],
      .dataRow #[some (ascii "1")],
      .errorResponse { fields := #[(83, "ERROR"), (67, "57014"), (77, "canceling statement")] },
      .ready .idle],
    .check "recovered" (·.isQuiescent)])

  runIO "empty query" (connectTrust ++ #[
    .send (.simpleQuery ""),
    .recv (emptyQueryResponse ++ readyForQuery 'I'),
    .expectEvents #[.emptyQuery, .ready .idle]])

  runIO "async messages interleave mid-query" (connectTrust ++ #[
    .send (.simpleQuery "SELECT pg_sleep(1)"),
    .recv (rowDescription #[col "pg_sleep" 2278] ++
      notification 42 "jobs" "job-1" ++
      row #[""] ++
      parameterStatus "application_name" "psql" ++
      commandComplete "SELECT 1" ++ readyForQuery 'I'),
    .expectEvents #[
      .rowDescription #[col "pg_sleep" 2278],
      .notification 42 "jobs" "job-1",
      .dataRow #[some ByteArray.empty],
      .parameterStatus "application_name" "psql",
      .commandComplete "SELECT 1",
      .ready .idle],
    .check "param updated" (·.parameter? "application_name" == some "psql")])

  runIO "notice during startup" #[
    .expectWrite startupGolden,
    .recv (noticeResponse "NOTICE" "01000" "connection logged"),
    .expectEvents #[.notice { fields := #[(83, "NOTICE"), (67, "01000"),
      (77, "connection logged")] }],
    .recv (authOk ++ readyForQuery 'I'),
    .expectEvents #[.authOk, .ready .idle]]

  runIO "fatal while quiescent" (connectTrust ++ #[
    .expectFatal (errorResponse "FATAL" "57P01" "terminating connection") .serverFatal])

  runIO "dataRow arity mismatch is fatal" (connectTrust ++ #[
    .send (.simpleQuery "SELECT 1"),
    .recv (rowDescription #[col "a" 23, col "b" 23]),
    .expectEvents #[.rowDescription #[col "a" 23, col "b" 23]],
    .expectFatal (row #["only-one"]) .protocol])

  -- ── extended protocol ───────────────────────────────────────────────────

  runIO "extended describe statement" (connectTrust ++ #[
    .sendExpect (.parse "s1" "SELECT $1::int4 + 1") (Frontend.parse "s1" "SELECT $1::int4 + 1"),
    .send (.describeStatement "s1"),
    .sendExpect .sync Frontend.sync,
    .recv (parseComplete ++ parameterDescription #[23] ++
      rowDescription #[col "?column?" 23] ++ readyForQuery 'I'),
    .expectEvents #[.parseComplete, .parameterDescription #[23],
      .rowDescription #[col "?column?" 23], .ready .idle]])

  runIO "extended execute happy path" (connectTrust ++ #[
    .send (.parse "" "SELECT 42"),
    .send (.bind "" ""),
    .send (.describePortal ""),
    .send (.execute ""),
    .send .sync,
    .recv (parseComplete ++ bindComplete ++ rowDescription #[col "?column?" 23] ++
      row #["42"] ++ commandComplete "SELECT 1" ++ readyForQuery 'I'),
    .expectEvents #[.parseComplete, .bindComplete, .rowDescription #[col "?column?" 23],
      .dataRow #[some (ascii "42")], .commandComplete "SELECT 1", .ready .idle],
    .check "quiescent" (·.isQuiescent)])

  runIO "extended error skips to sync, pipelined segment survives" (connectTrust ++ #[
    .send (.parse "bad" "SELECT * FROM missing"),
    .send (.bind "" "bad"),
    .send (.execute ""),
    .send .sync,
    .send (.parse "ok" "SELECT 1"),
    .send .sync,
    .recv (errorResponse "ERROR" "42P01" "relation does not exist"),
    .expectEvents #[.errorResponse { fields :=
      #[(83, "ERROR"), (67, "42P01"), (77, "relation does not exist")] }],
    .send (.parse "late" "SELECT 2"),  -- recovery armed: queues behind the drain
    .recv (readyForQuery 'I'),
    .expectEvents #[.ready .idle],
    .recv (parseComplete ++ readyForQuery 'I'),
    .expectEvents #[.parseComplete, .ready .idle],
    .recv parseComplete,
    .expectEvents #[.parseComplete],
    .check "quiescent" (·.isQuiescent)])

  runIO "flush abort gates submits until user sync" (connectTrust ++ #[
    .send (.parse "p" "SELECT broken"),
    .sendExpect .flush Frontend.flush,
    .recv (errorResponse "ERROR" "42601" "syntax error"),
    .expectEvents #[.errorResponse { fields :=
      #[(83, "ERROR"), (67, "42601"), (77, "syntax error")] }],
    .reject (.execute "") .rejectedAborted,
    .reject (.parse "q" "SELECT 1") .rejectedAborted,
    .reject (.simpleQuery "SELECT 1") .rejectedAborted,
    .send .sync,
    .recv (readyForQuery 'I'),
    .expectEvents #[.ready .idle],
    .check "recovered" (·.isQuiescent)])

  runIO "portal suspend and resume" (connectTrust ++ #[
    .send (.parse "" "SELECT generate_series(1,5)"),
    .send (.bind "c" ""),
    .sendExpect (.execute "c" 2) (Frontend.execute "c" 2),
    .send .flush,
    .recv (parseComplete ++ bindComplete ++ row #["1"] ++ row #["2"] ++ portalSuspended),
    .expectEvents #[.parseComplete, .bindComplete, .dataRow #[some (ascii "1")],
      .dataRow #[some (ascii "2")], .portalSuspended],
    .send (.execute "c" 2),
    .send .flush,
    .recv (row #["3"] ++ row #["4"] ++ portalSuspended),
    .expectEvents #[.dataRow #[some (ascii "3")], .dataRow #[some (ascii "4")],
      .portalSuspended],
    .send (.execute "c" 2),
    .send (.closePortal "c"),
    .send .sync,
    .recv (row #["5"] ++ commandComplete "SELECT 5" ++ closeComplete ++ readyForQuery 'I'),
    .expectEvents #[.dataRow #[some (ascii "5")], .commandComplete "SELECT 5",
      .closeComplete, .ready .idle]])

  runIO "pipeline of three segments, middle fails" (connectTrust ++ #[
    .send (.parse "a" "SELECT 1"),
    .send (.bind "" "a"),
    .send (.execute ""),
    .send .sync,
    .send (.parse "b" "SELECT * FROM missing"),
    .send (.bind "" "b"),
    .send (.execute ""),
    .send .sync,
    .send (.parse "c2" "SELECT 3"),
    .send (.bind "" "c2"),
    .send (.execute ""),
    .send .sync,
    .recv (parseComplete ++ bindComplete ++ row #["1"] ++ commandComplete "SELECT 1" ++
      readyForQuery 'I' ++
      errorResponse "ERROR" "42P01" "nope" ++ readyForQuery 'I' ++
      parseComplete ++ bindComplete ++ row #["3"] ++ commandComplete "SELECT 1" ++
      readyForQuery 'I'),
    .expectEvents #[
      .parseComplete, .bindComplete, .dataRow #[some (ascii "1")],
      .commandComplete "SELECT 1", .ready .idle,
      .errorResponse { fields := #[(83, "ERROR"), (67, "42P01"), (77, "nope")] },
      .ready .idle,
      .parseComplete, .bindComplete, .dataRow #[some (ascii "3")],
      .commandComplete "SELECT 1", .ready .idle],
    .check "quiescent" (·.isQuiescent)])

  runIO "unnamed statement reuse" (connectTrust ++ #[
    .send (.parse "" "SELECT 1"),
    .send (.bind "" ""),
    .send (.execute ""),
    .send (.parse "" "SELECT 2"),
    .send (.bind "" ""),
    .send (.execute ""),
    .send .sync,
    .recv (parseComplete ++ bindComplete ++ row #["1"] ++ commandComplete "SELECT 1" ++
      parseComplete ++ bindComplete ++ row #["2"] ++ commandComplete "SELECT 1" ++
      readyForQuery 'I'),
    .expectEvents #[
      .parseComplete, .bindComplete, .dataRow #[some (ascii "1")], .commandComplete "SELECT 1",
      .parseComplete, .bindComplete, .dataRow #[some (ascii "2")], .commandComplete "SELECT 1",
      .ready .idle]])

  -- ── COPY subprotocol ────────────────────────────────────────────────────

  runIO "copy in happy path" (connectTrust ++ #[
    .send (.simpleQuery "COPY t FROM STDIN"),
    .recv (copyInResponse 0 #[0, 0]),
    .expectEvents #[.copyInStarted ⟨false, #[0, 0]⟩],
    .reject (.parse "p" "SELECT 1") .rejectedInvalid,  -- direction reversed
    .reject (.simpleQuery "SELECT 1") .rejectedInvalid,
    .sendExpect (.copyData (ascii "1\ta\n")) (Frontend.copyData (ascii "1\ta\n")),
    .send (.copyData (ascii "2\tb\n")),
    .sendExpect .copyDone Frontend.copyDone,
    .recv (commandComplete "COPY 2" ++ readyForQuery 'I'),
    .expectEvents #[.commandComplete "COPY 2", .ready .idle],
    .check "quiescent" (·.isQuiescent)])

  runIO "copy in client abort" (connectTrust ++ #[
    .send (.simpleQuery "COPY t FROM STDIN"),
    .recv (copyInResponse 0 #[]),
    .expectEvents #[.copyInStarted ⟨false, #[]⟩],
    .send (.copyData (ascii "1\n")),
    .sendExpect (.copyFail "source failed") (Frontend.copyFail "source failed"),
    .recv (errorResponse "ERROR" "57014" "COPY from stdin failed" ++ readyForQuery 'I'),
    .expectEvents #[.errorResponse { fields :=
      #[(83, "ERROR"), (67, "57014"), (77, "COPY from stdin failed")] }, .ready .idle],
    .check "recovered" (·.isQuiescent)])

  runIO "copy in server abort mid-stream" (connectTrust ++ #[
    .send (.simpleQuery "COPY t FROM STDIN"),
    .recv (copyInResponse 0 #[]),
    .expectEvents #[.copyInStarted ⟨false, #[]⟩],
    .send (.copyData (ascii "bad\n")),
    .recv (errorResponse "ERROR" "22P02" "invalid input"),
    .expectEvents #[.errorResponse { fields :=
      #[(83, "ERROR"), (67, "22P02"), (77, "invalid input")] }],
    .reject (.copyData (ascii "more\n")) .rejectedInvalid,  -- copy is over
    .recv (readyForQuery 'I'),
    .expectEvents #[.ready .idle],
    .check "recovered" (·.isQuiescent)])

  runIO "copy out" (connectTrust ++ #[
    .send (.simpleQuery "COPY t TO STDOUT"),
    .recv (copyOutResponse 0 #[0] ++ copyData (ascii "1\ta\n") ++
      copyData (ascii "2\tb\n") ++ copyDone ++ commandComplete "COPY 2" ++
      readyForQuery 'I'),
    .expectEvents #[.copyOutStarted ⟨false, #[0]⟩, .copyData (ascii "1\ta\n"),
      .copyData (ascii "2\tb\n"), .copyOutDone, .commandComplete "COPY 2", .ready .idle]])

  runIO "copy with pipelined op behind it is fatal" (connectTrust ++ #[
    .send (.simpleQuery "COPY t FROM STDIN"),
    .send (.simpleQuery "SELECT 1"),
    .expectFatal (copyInResponse 0 #[]) .protocol])

  runIO "3.2 negotiation" (#[
    Step.expectWrite (encodeStartup #[("user", "user"), ("client_encoding", "UTF8")]
      protocolVersion32),
    .recv (negotiateProtocolVersion 196608 #["_pq_.fancy"]),  -- full code, as PG sends
    .expectEvents #[.negotiatedVersion .v3_0 #["_pq_.fancy"]],
    .recv (authOk ++ backendKeyData 7 (hex "00 00 00 01") ++ readyForQuery 'I'),
    .expectEvents #[.authOk, .ready .idle]] : Script)
    { cfg := { testConfig with requestedVersion := .v3_2 } }

  IO.println "all flow assertions passed"
