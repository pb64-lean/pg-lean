# pg-lean

A PostgreSQL client for Lean 4, built as an extension of the standard
library's networking foundations (`Std.Async.TCP`), with the eventual goal of
an upstream contribution. The PostgreSQL protocol and TLS 1.3 state machines
are pure Lean; TLS cryptography uses the sibling `tls13-lean` HACL* bindings
for formally verified, constant-time primitives.

Bazel + `rules_lean` project, sibling to `../tls13-lean`, `../rules_lean`, and
`../grpc-lean` (same pinned nix Lean toolchain).

## Status

Complete against the project's conformance bar: every item of the plaintext
live checklist passes on **PostgreSQL 17 and 18** across **trust,
SCRAM-SHA-256, cleartext-password, and md5 (17)** authentication, over wire
protocol **3.0 and 3.2** (18 accepts 3.2 with variable-length cancel keys; 17
negotiates down via NegotiateProtocolVersion). The full TLS 1.3 checklist
passes on PostgreSQL 17 and 18 with trust authentication and on PostgreSQL 18
with SCRAM-SHA-256.

```
$ scripts/pg-live.sh 18 scram tls
PASS transport.sslmode             PASS errors.field_completeness
PASS simple.shapes                 PASS notices.raise_notice
PASS extended.prepare_describe     PASS unicode.identifiers_data
PASS extended.portal_suspend       PASS bigrow.10mb
PASS codec.param_roundtrip         PASS copy.roundtrip_100k
PASS pipeline.mid_error            PASS notify.cross_connection
PASS tx.status_tracking            PASS cancel.pg_sleep
PASS protocol.negotiate_3_2
ALL PASS
```

## Usage

```lean
import Pg

def demo : IO Unit := do
  -- `verify-full` authenticates both the certificate chain and server name.
  let conn ← Pg.connectUri
    "postgres://bill:secret@localhost:5432/mydb?sslmode=verify-full&sslrootcert=/path/to/root.crt"
  -- simple query (multi-statement capable)
  let results ← conn.query "SELECT id, name FROM users WHERE active"
  match results with
  | .ok rows =>
    for i in [0:rows[0]!.rows.size] do
      let id ← IO.ofExcept (rows[0]!.get (α := Int) i 0)
      let name ← IO.ofExcept (rows[0]!.getByName (α := String) i "name")
      IO.println s!"{id}: {name}"
  | .error e => IO.eprintln (toString e)   -- SQLSTATE preserved: e.sqlState?
  -- extended protocol with typed parameters
  let _ ← conn.prepare "by_id" "SELECT name FROM users WHERE id = $1"
  let _ ← conn.execute "by_id" #[some "42".toUTF8]
  -- COPY, LISTEN/NOTIFY, cancellation
  let _ ← conn.copyInChunks "COPY t FROM STDIN" #["1\ta\n".toUTF8]
  let _ ← conn.listen "events"
  let _ ← conn.waitNotification 1000
  conn.cancel   -- from another task, via a separate CancelRequest connection
  conn.close
```

`pg_lean` (`Cmd/PgLean.lean`) is the command-line query client — a minimal
non-interactive psql that works against any supported connection (all auth
modes, TLS options, protocol 3.2). One-shot statements via the simple
protocol, or a prepared statement with parameters via `-e`:

```
bazel run //Cmd:pg_lean -- postgres://postgres@localhost/postgres "SELECT version()"
bazel run //Cmd:pg_lean -- -e -b postgres://postgres@localhost/postgres \
    'SELECT $1::int4 + $2::int4' 40 2        # extended protocol, binary results
```

## Feature surface

- **Startup/auth**: trust, cleartext password, md5, SCRAM-SHA-256, and
  SCRAM-SHA-256-PLUS with `tls-server-end-point` channel binding (pure-Lean
  crypto, RFC 7677-vector-tested, server signature verified — mutual auth).
  `channel_binding=prefer` is the default and chooses PLUS whenever a TLS
  server offers it; `require` fails closed without PLUS; `disable` forces
  ordinary SCRAM.
- **TLS 1.3** after PostgreSQL `SSLRequest`: ChaCha20-Poly1305/SHA-256 with
  first-flight X25519 and P-256 key shares, incremental records, Finished
  and CertificateVerify signature verification, session-ticket handling,
  peer-initiated KeyUpdate, alerts, and close_notify. All six libpq
  `sslmode` values are active: `verify-ca` validates the X.509 path and
  validity window, while `verify-full` additionally verifies the DNS name or
  IP address.
  `allow`/`prefer` retry the alternate transport only for PostgreSQL's `N`
  response or the standard English pg_hba transport-mismatch FATAL; other TLS
  failures fail closed instead of permitting a silent downgrade.
- **Simple query** incl. multi-statement and empty-query; **extended query**
  (Parse/Bind/Describe/Execute/Close/Flush/Sync), named statements, portals
  with suspension/resume, parameter + result formats (text and binary).
- **Pipelining** with the protocol's error recovery: skip-until-Sync, and
  Flush-driven aborts gate submits until the user supplies a Sync
  (libpq's `PGRES_PIPELINE_ABORTED` analogue).
- **COPY IN/OUT** streaming; **LISTEN/NOTIFY** with a notification queue and
  selector-based waits; **cancellation** via separate-connection
  CancelRequest (3.0 4-byte and 3.2 variable-length keys), with a fresh TLS
  handshake when the original connection used TLS.
- **Codecs** (text + binary): bool, int2/4/8, float4/8, text/varchar/bpchar,
  bytea, uuid, json/jsonb, date/time/timestamp/timestamptz on `Std.Time`
  (PG↔Unix epoch handled), `PgNumeric` (lossless base-10000), `PgInterval`
  (months/days/micros), 1-D arrays with NULLs.
- **Errors**: full §53.8 field set with accessors (SQLSTATE, constraint,
  table, position, ...); statement errors are values, connection-fatal
  errors are typed separately.
- **Protocol 3.0 default, 3.2 opt-in** (`?protocol=3.2` or
  `requestedVersion := .v3_2`) with NegotiateProtocolVersion downgrade.
  Note: servers send the *full* version code (196608) in
  NegotiateProtocolVersion despite the docs saying "newest minor" — both
  encodings are accepted.
- Connect timeouts, `postgres://` URI subset (percent-decoding, libpq-style
  query keywords, `connect_timeout`, `sslrootcert`, `channel_binding`, and all
  six `sslmode` spellings). Verifying modes resolve trust in libpq order:
  explicit `sslrootcert`, `PGSSLROOTCERT`, then `~/.postgresql/root.crt`.
  The programmatic `sslMode` default remains `disable` for compatibility with
  pre-TLS pg-lean; request TLS `prefer` or `require` explicitly.

## Security compromises (by design, documented)

| Area | Status | Notes |
|---|---|---|
| SCRAM-SHA-256 | Full, pure Lean | SHA-256/HMAC/PBKDF2 implemented here; FIPS/RFC vectors in `bazel test` |
| SASLprep (RFC 4013) | Partial | ASCII exact (SASLprep is identity); non-ASCII passwords sent as raw UTF-8 (matches several production drivers; works against PG in practice) |
| md5 auth | Full | Deprecated in PG 18 but still live-tested on 17 |
| Cleartext auth | Full | Plaintext on the wire — see TLS row |
| TLS 1.3 encryption | Partial | HACL* ChaCha20-Poly1305/SHA-256 with X25519/P-256; PostgreSQL SSLRequest path only (not PG 17+ direct negotiation) |
| TLS server identity | Authenticated in verification modes | CertificateVerify proof-of-possession is mandatory in every TLS mode. `verify-ca` validates the X.509 chain, validity, CA constraints, KeyUsage, and critical extensions; `verify-full` additionally verifies SAN/CN hostname or byte-exact IP identity. `require` deliberately encrypts without authenticating a CA-trusted server identity. CRL/OCSP revocation is not implemented, matching libpq's default behavior |
| SCRAM-SHA-256-PLUS | Supported | `tls-server-end-point` binds SCRAM to this connection's exact leaf certificate. This detects a TLS-terminating credential-relay MITM even under `sslmode=require` without CA trust. `channel_binding=prefer` (default), `require`, and `disable` match libpq policy |
| GSSAPI / SSPI / Kerberos | Unsupported | Enterprise SSO out of scope |
| CSPRNG | `IO.getRandomBytes` | Per-connection SCRAM nonces, ClientHello randoms, and ephemeral ECDHE scalars |
| Timing side channels | Mixed | HACL* primitives are constant-time; Lean protocol/control code makes no timing guarantees |

## Architecture

Sans-IO core + thin async shell (the grpc-lean/PostgresNIO pattern):

- `Pg/Protocol/Message.lean` — byte layer: BE primitives, tagged framing,
  incremental `DecodeState`, startup-phase messages.
- `Pg/Protocol/Backend.lean` / `Frontend.lean` — the full typed message
  catalog (decoders / encoders).
- `Pg/Protocol/Machine.lean` — **pure** connection state machine: phases
  startup/running/closed ("ready" is just an empty pipeline), a pipeline of
  op descriptors with per-op reply progress, `step`/`feed` (server-driven)
  and `submit` (user-driven) with a three-way error taxonomy: fatal =
  `Except.error` (no state to continue with — poisoned by construction),
  recoverable server errors = events + internal drain/abort transitions,
  user mistakes = rejections that leave state untouched. Zero `partial`.
- `Pg/Crypto/*`, `Pg/Sasl/Scram.lean` — pure crypto + the SCRAM sub-machine.
- `Pg/Tls/Handshake.lean`, `Record.lean`, `Client.lean`, `TrustStore.lean` —
  pure, incremental TLS codecs, authenticated record layer, transcript/key
  schedule, sans-IO client machine, and libpq-style trust-store resolution
  over `tls13-lean`'s HACL* and X.509 primitives.
- `Pg/Types/*` — OIDs, `PgDecode`/`PgEncode`, `PgNumeric`, `PgInterval`.
- `Pg/Connection.lean` — async shell over `Std.Async.TCP`: DNS, Mutex-held
  exchanges, notification queue (`recvSelector` raced against timers via
  `Selectable.one`), PostgreSQL SSL negotiation and TLS transport, COPY pumps,
  cancel.
- `Cmd/PgProbe.lean`, `Integration/LiveTest.lean` — probing CLI + checklist.

## Testing (the yardstick)

Hermetic, every commit — `bazel test //...` (10 suites):
crypto vectors (FIPS 180-4, RFC 4231, PBKDF2, RFC 1321, RFC 4648), the RFC
7677 SCRAM exchange byte-for-byte, hand-frozen wire goldens for the whole
message catalog + fragmentation torture + corrupt-payload rejection, machine
unit tests (submit gating, taxonomy, abort recovery), scripted full-protocol
flows each re-run under 1/3/7-byte chunking, codec KATs, and an in-process
fake server over real loopback TCP. The TLS suite adds record limit/tamper
tests and deterministic full handshakes for X25519 and P-256, hostile transport
fragmentation, Finished/CertificateVerify failure, strict Certificate-list
capture, application traffic, tickets, peer-initiated KeyUpdate, and
close_notify.

Live, on demand —
`scripts/pg-live.sh [17|18] [trust|scram|password|md5] [plain|tls|tls-verify|tls-cb]`
runs against disposable Docker containers.
`plain`/`tls` execute the 15-item conformance checklist; `tls-verify` generates
throwaway roots and server certificates and proves trusted `verify-full`,
unknown-CA rejection, hostname separation between `verify-ca` and
`verify-full`, self-signed policy, and expiry rejection. `tls-cb` (with
`scram`) proves that `require` and TLS `prefer` negotiate
SCRAM-SHA-256-PLUS, plaintext `require` fails closed, and plaintext `prefer`
uses ordinary SCRAM-SHA-256.

## Toolchain notes

Bazel builds with the pinned nix Lean (4.31-pre; `Std.Async.*` namespaces).
The host/editor toolchain (4.27) uses `lakefile.lean` for LSP only — restart
the language server after first checkout. Verify Lean sources with
`~/.elan/bin/lean +grpc-lean-nix-4.31`, not the host lean: 4.31 renamed
`Array.mkArray`→`replicate` and returns `String.Slice` from
`trimAscii`/`drop`; `Std.Time` Offsets are `UnitVal` structures.

## Remaining work

- CRL/OCSP certificate revocation checking for X.509 verification modes.
- PostgreSQL direct TLS negotiation (`sslnegotiation=direct`, ALPN
  `postgresql`), AES-GCM suites, and HelloRetryRequest.
- Full SASLprep (NFKC tables) for non-ASCII passwords.
- Connection pooling; a background reader task (today: single in-flight
  operation per connection, notifications queue during operations).
- `date`/`timestamp` ±infinity (Std.Time has no representation; currently a
  decode error), BC dates, multi-dimensional arrays, exotic types via an
  extensible registry.
- Unix-domain sockets, multi-host URIs, GSSAPI.
