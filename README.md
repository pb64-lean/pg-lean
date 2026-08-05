# pg-lean

[![CI](https://github.com/pb64-lean/pg-lean/actions/workflows/ci.yml/badge.svg?branch=main)](https://github.com/pb64-lean/pg-lean/actions/workflows/ci.yml) [![PG live](https://github.com/pb64-lean/pg-lean/actions/workflows/pg-live.yml/badge.svg?branch=main)](https://github.com/pb64-lean/pg-lean/actions/workflows/pg-live.yml) [![Assurance](https://github.com/pb64-lean/pg-lean/actions/workflows/assurance.yml/badge.svg?branch=main)](https://github.com/pb64-lean/pg-lean/actions/workflows/assurance.yml)

A PostgreSQL client for Lean 4 built on the standard library's networking
foundations (`Std.Async.TCP`). The PostgreSQL protocol and TLS 1.3 state
machines are pure Lean; TLS cryptography uses the sibling `tls13-lean` HACL*
bindings for formally verified, constant-time primitives.

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

open Std.Async

def demo : Async Unit := do
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

-- Block once, at the executable boundary; library callers compose `demo`
-- directly with other cooperative `Async` work.
def main : IO Unit := demo.block
```

Connection and query operations return `Std.Async.Async`. Multiple callers may
submit bounded batches to one connection concurrently; none of them drives the
socket or occupies a worker while waiting for its reply.

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
- **Concurrent, owner-tagged pipelining**: bounded batches are admitted and
  written in coordinator order, while one background reader attributes every
  reply to the submitting caller. Admission enforces that extended batches end
  in their own Sync and that a simple query is a batch of its own, so
  skip-until-Sync recovery cannot cross an owner boundary
  (`taggedStep_error_stays_in_batch`). Generic `run` rejects ambiguous
  multi-boundary, mixed extended/simple-query, and protocol-control batches.
- **COPY IN/OUT** streaming with exclusive connection ownership for the COPY
  lifetime; **LISTEN/NOTIFY** with an independent queue that receives messages
  even while no request is pending; **cancellation** via separate-connection
  CancelRequest (3.0 4-byte and 3.2 variable-length keys), with a fresh TLS
  handshake when the original connection used TLS.
- **Codecs** (text + binary): bool, int2/4/8, float4/8, text/varchar/bpchar,
  bytea, uuid, json/jsonb, date/time/timestamp/timestamptz on `Std.Time`
  (PG↔Unix epoch handled), `PgNumeric` (lossless base-10000), `PgInterval`
  (months/days/micros), 1-D arrays with NULLs (`renderArrayText` sends one as
  a text parameter).
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
  The programmatic `sslMode` default is `disable`; request TLS `prefer` or
  `require` explicitly.

## Security compromises (by design, documented)

| Area | Status | Notes |
|---|---|---|
| SCRAM-SHA-256 | Full, pure Lean | SHA-256/HMAC/PBKDF2 implemented here; FIPS/RFC vectors in `bazel test` |
| SASLprep (RFC 4013) | Partial | ASCII exact (SASLprep is identity); non-ASCII passwords sent as raw UTF-8 (matches several production drivers; works against PG in practice) |
| md5 auth | Full | Deprecated in PG 18; live-tested on 17 |
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
- `Pg/Types/*` — OIDs, `PgDecode`/`PgEncode`, `PgNumeric`, `PgInterval`. Every
  codec is explicit recursion, not a `for` loop over mutable state: a `forIn`
  body is opaque to the kernel, so the roundtrip laws would not be statable.
- `Pg/Connection.lean` — cooperative shell over `Std.Async.TCP`: one reader,
  one writer, and a short-held coordinator that assigns owner tags, advances
  the pure machine, seals TLS records, and inserts socket-ready bytes in the
  same order. User callbacks, COPY producers/sinks, notification waits, and
  all socket waits run outside the coordinator. COPY is exclusive; ordinary
  bounded batches pipeline concurrently. Only CLI/test `main` functions call
  `Async.block`.
- `Cmd/PgProbe.lean`, `Integration/LiveTest.lean` — probing CLI + checklist.

## Proved properties (kernel-checked, no `sorry`, core + Std only)

Machine-checked theorems live next to the code they describe; each module's
section docstring states its scope.

- **Framing** (`Pg/Protocol/Message.lean`) — byte conservation, partition
  invariance (a byte stream decodes the same however it is chunked), totalized
  buffered parsing.
- **Machine invariants** (`Pg/Protocol/Machine.lean`) — `State.WellFormed`
  preserved by `submit`/`submitAll`/`step`/`feed`; `feed` factored through the
  framing decoder with exact byte accounting.
- **Correlation / FIFO attribution** — the shell's event-driven completion FIFO
  (`shellStep`) is proved to equal the machine's pending-op queue
  (`Pipeline.pending`) after every accepted message (`step_fifo`,
  `runSteps_fifo`, `feed_fifo`) and submission (`submit_fifo`). Headline:
  `terminal_pops_head` — every user-visible success pops exactly the head
  operation, in submission order, COPY included — with
  `nonterminal_preserves_fifo` and `error_drops_to_sync` as complements. The
  owner-tagged refinement proves erasing owner metadata commutes with recovery,
  each event, whole feeds, and append; `tagged_terminal_pops_head` proves a
  terminal event removes exactly the tagged head used by the live
  coordinator's completion criterion. For the batch shapes admission allows,
  error recovery is owner-local: `taggedStep_error_stays_in_batch` proves a
  server error on a validated extended batch drops ops only up to that batch's
  own trailing Sync (never a later owner's), and
  `taggedStep_error_keeps_simpleQuery` that a lone simple query drops nothing
  at all.
- **Startup ordering** — `AuthStep`/`AuthReach` are PostgreSQL's documented
  authentication sequences; `step_startup_order` and `runSteps_startup_order`
  prove the machine refines them, `authStep_stage_le` that the exchange never
  runs backwards, `authStep_scram` that SCRAM's server-signature check can
  never be skipped, and `startup_ready` that a completed startup enters
  `running` with an empty pipeline.
- **Progress and completion** — `step_progress` (an expected reply always
  steps), `step_errorResponse_progress` (a server error never poisons a
  mid-pipeline connection), `expectedReply_nonempty` (the expected-reply table
  is nowhere vacuous), and per-`OpKind` completion: the documented reply
  sequence pops the operation, for Parse/Bind/Close/Describe/Sync, Execute with
  any number of streamed rows, Execute over COPY IN and COPY OUT, and the
  simple-query cycle.
- **SCRAM** (`Pg/Sasl/Scram.lean`) — construction laws,
  `parseServerFirst_render` (render→parse roundtrip), and `verifyServerFinal`'s
  byte-exact mutual-authentication spec.
- **TLS policy** (`Pg/Config.lean`) — `sslmode` is a single decision table that
  `connect`, peer verification, and trust-store loading all read;
  `policy_no_insecure_fallback` proves no encryption-requiring mode may retry
  in a weaker transport.
- **Connection strings** (`Pg/Config.lean`) — `percentDecode_percentEncode`
  (percent-encoding roundtrips every byte, so non-ASCII passwords such as the
  live suite's `pg-lean-läuft` survive), `parseUri_renderUri` (parsing a
  rendered URI recovers user, password, host, port, and database),
  `applyQueryParam_unknown` and `applyQueryPairs_render` (unknown query
  parameters can neither fail the parse nor disturb a recognized setting, and
  land in `parameters` in order). The two halves join in
  `parseUri_renderUri_query`: **rendering a config together with its startup
  parameters produces a URI that parses back to both** — the authority, path
  *and* every query field, in order. The supporting
  `splitAllChar_renderQuery` lemma proves that a rendered query string splits
  back into exactly its fields.
- **Codecs** (`Pg/Types/Codec.lean`) — text and binary integer roundtrips and
  `PgInterval.fromBinary_toBinary`; `PgNumeric.fromBinary_toBinary` — **binary
  `numeric` is lossless**: sign, weight, display scale and every base-10000
  digit are recovered exactly, under the wire's own limits (the three header
  counts are `int16` fields, digits are below 10000), with
  `fromBinary_toBinary_special` for NaN/±Infinity; and the temporal text
  codecs — `parseDate_renderDate` (a rendered AD date parses back to the same
  `PlainDate`), `parseTimeNanos_renderTimeNanos` (a rendered time-of-day parses
  back to the same nanosecond count, at PostgreSQL's microsecond resolution),
  and `timestampFields_renderTimestamp` (a rendered timestamp splits back into
  that date and those nanoseconds). Underneath them, in
  `Pg/Types/Digits.lean`, `parseNatField_padDigits`: a zero-padded decimal
  field reads back as the number it was rendered from, at any width. That
  module is the kernel-visible decimal substrate every text codec is proved
  through — core's `Nat.repr`/`String.toNat?`/`String.splitOn` are all opaque
  to the kernel, so pg-lean renders and parses decimals with its own
  `natDigits`/`padDigits`/`natOfDigits` and splits with `List.splitOn`.

  On the text side, `PgNumeric.fromString_toString` — **a rendered `numeric`
  parses back to the same value**: every base-10000 digit, the sign, the
  weight and the display scale, with no precision lost in the regrouping. It
  holds for every `PgNumeric.Canonical` value, which is what PostgreSQL sends:
  digits in base-10000 range, no leading or trailing zero group, zero spelled
  canonically, and a display scale wide enough to reach the last digit. (Those
  hypotheses are the law, not fine print — without the last one the rendering
  genuinely truncates, and the theorem would be false.) The lemma the whole
  argument turns on is `PgNumeric.group4_flatMap`: regrouping a rendered digit
  string four characters at a time returns exactly the groups it came from.

  For `interval`, the text side matches the binary one:
  `PgInterval.fromString_toString` — **a rendered interval parses back to the
  same triple**, unconditionally. Months, days and microseconds are
  independent (a month is not a fixed number of days), the sign and the
  sub-second fraction survive, and no side condition is needed.

  For 1-D arrays, `decode_encode_array`: an array of element texts sent as a
  text parameter is read back by `decodeValue` as the same array, NULLs
  included — and an element whose text is literally `NULL` stays a value,
  because `renderArrayText` quotes every non-NULL element (escaping `"` and
  `\`). The parser-level half is `parseArrayText_renderArrayText`; lifting it
  to the public API needs "`Array.mapM` with a function that never fails
  succeeds", which core does not have for a `match`-shaped function
  (`mapM_ok_of_pure`, via `funext` into `Array.mapM_pure`).

  Two gaps are deliberate. **Floats are excluded**: `toString`/`parseFloat` is
  not an unconditional IEEE-754 roundtrip, and stating the true law needs
  real-arithmetic support this repository does not have (core + Std only). And
  the temporal laws stop where `Std.Time` begins: `PlainTime.ofNanoseconds` and
  the `Timestamp` epoch conversions are not reasoned about (`Std.Time` ships no
  lemmas and does not expose its definitions), so the laws cover the text
  codecs pg-lean actually owns.

### Mechanically enforced

Four `lean_assurance_test` targets audit the compiled environment at build
time, so a regression is a red build rather than a stale claim:

| target | scope |
| --- | --- |
| `//Pg/Protocol:protocol_assurance` | framing, `State.WellFormed`, FIFO attribution, byte accounting, progress/recovery, startup order, the ten `completes_*` |
| `//Pg/Types:types_assurance` | codec roundtrips (integers, `numeric`, `interval`, temporal text) |
| `//Pg/Sasl:sasl_assurance` | SCRAM construction and mutual authentication |
| `//:pg_lean_assurance` | the whole client: `sslmode` policy, trust-store gate, connection-string roundtrips |

Each target checks that its named theorems match their pinned statements
definitionally and close over an allowed axiom set — and scans **every**
first-party module (`module_prefixes = ["Pg"]`, 22 modules / ~4600 constants)
for `sorry`, stray axioms, `unsafe`, and `@[extern]`. Exact mode is a closed
world at module granularity: every module the audited environment imports must
be covered by `module_prefixes`, by `unaudited_module_prefixes`, or by the
toolchain allowlist. The root target declares `HaclStar`/`TLS13`/`Tls` as
unaudited here because the tls13-lean sibling's own assurance targets audit
them; the three per-library targets import nothing outside `Pg` and the
toolchain, so importing an unlisted module anywhere fails the build.
The whole-client inventory contains no `sorry`, no `unsafe`, no `opaque`, four
`partial` definitions (the pinned socket/channel loops `recvTransport`,
`readerLoop`, `writerLoop`, and `pumpCopyOut` in `Pg/Connection.lean`), and
**no `@[extern]` constants at all** — the expected extern inventory is empty,
so any first-party native code would fail the audit. pg-lean's crypto is pure
Lean; the only native code it runs is `tls13-lean`'s HACL* bindings, audited
in that repository.

The allowed axiom set is **exactly the standard three** — `propext`,
`Classical.choice`, `Quot.sound` — and the scan reports `declared axioms in
scope: none`. There is no `sorry`, no `native_decide`, and no SAT/LRAT
certificate anywhere in the trusted surface.

The big-endian byte (de)composition proofs operate at the `Nat` level:
`Nat.shiftLeft_add_eq_or_of_lt` turns a disjoint `|||` into `+` (`or_add_lt`),
and `omega` decides the extraction identities over `/` and `%` by literal
powers of two. See `pack_nat16`/`pack_nat32`/`unpack_pack16`/`unpack_pack32` in
[`Pg/Protocol/Message.lean`](Pg/Protocol/Message.lean) and
`pack_nat64`/`unpack_pack64` in [`Pg/Types/Codec.lean`](Pg/Types/Codec.lean).
Neither module imports `Std.Tactic.BVDecide`; any axiom outside the three-item
allowlist fails every assurance target and requires explicit policy approval.

## Testing (the yardstick)

Hermetic — `bazel test //...` (10 suites):
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
The host/editor toolchain (4.27) uses `lakefile.lean` for LSP only. Restart the
language server when initializing the checkout. Verify Lean sources with
`~/.elan/bin/lean +grpc-lean-nix-4.31`, not the host Lean: the build API uses
`Array.replicate`, returns `String.Slice` from `trimAscii`/`drop`, and represents
`Std.Time` offsets as `UnitVal` structures.

## Unsupported surface

- CRL/OCSP certificate revocation checking for X.509 verification modes.
- PostgreSQL direct TLS negotiation (`sslnegotiation=direct`, ALPN
  `postgresql`), AES-GCM suites, and HelloRetryRequest.
- Full SASLprep (NFKC tables) for non-ASCII passwords.
- Connection pooling and bounded/backpressured queues for applications that
  need explicit memory caps under sustained pipeline or COPY load.
- `date`/`timestamp` ±infinity (Std.Time has no representation; decoding
  returns an error), BC dates, multi-dimensional arrays, exotic types via an
  extensible registry.
- Unix-domain sockets, multi-host URIs, GSSAPI.
