import Pg.Connection
import Pg.Config
import Pg.Types.Codec
import Pg.Crypto.Hex

/-!
Live conformance checklist, run on demand against a real server (never part
of `bazel test`): `PG_URL=postgres://... bazel run //Integration:pg_live_test`, or via
`scripts/pg-live.sh [17|18] [trust|scram|password|md5]
[plain|tls|tls-verify|tls-cb]`. The lightweight
`--connect URL` mode performs one connection and `SELECT 1`; the live TLS
identity matrix uses it for expected-success and expected-failure probes.
`--connect-expect-mechanism URL MECHANISM` additionally checks the exact
SASL mechanism selected by the client.
One PASS/FAIL line per checklist item; nonzero exit on any failure. Full pass
across {17,18} × {trust,scram,password,md5(17)} is the project's "complete"
bar.
-/

open Pg
open Pg.Protocol

structure Ctx where
  url : String
  failures : IO.Ref Nat

def item (ctx : Ctx) (name : String) (act : IO (Option String)) : IO Unit := do
  match ← try act catch e => pure (some s!"exception: {e}") with
  | none => IO.println s!"PASS {name}"
  | some why =>
    IO.println s!"FAIL {name}: {why}"
    ctx.failures.modify (· + 1)

def ok! (r : Except Error α) : IO α :=
  match r with
  | .ok v => pure v
  | .error e => throw (IO.userError (toString e))

def expectIs (cond : Bool) (why : String) : IO (Option String) :=
  pure (if cond then none else some why)

def okEq [BEq α] (r : Except String α) (v : α) : Bool :=
  match r with
  | .ok x => x == v
  | .error _ => false

def readyStatuses (events : Array Machine.Event) : Array TxStatus :=
  events.filterMap fun
    | .ready tx => some tx
    | _ => none

def serverErrors (events : Array Machine.Event) : Array ErrorFields :=
  events.filterMap fun
    | .errorResponse fields => some fields
    | _ => none

-- ── items ──────────────────────────────────────────────────────────────────

def copyRoundtrip (ctx : Ctx) : IO (Option String) := do
  let conn ← connectUri ctx.url
  let _ ← ok! (← conn.exec "CREATE TEMP TABLE copy_test (id int4, label text)")
  let rows := 100000
  let chunk ← IO.mkRef 0
  let tagIn ← ok! (← conn.copyIn "COPY copy_test FROM STDIN" do
    let i ← chunk.get
    if i ≥ rows then
      pure none
    else do
      let mut buf := ByteArray.empty
      for j in [i:min rows (i + 5000)] do
        buf := buf ++ s!"{j}\tvalue-{j}\n".toUTF8
      chunk.set (i + 5000)
      pure (some buf))
  if tagIn != s!"COPY {rows}" then
    return some s!"copy in tag {tagIn}"
  let check ← ok! (← conn.query "SELECT count(*), sum(id)::int8 FROM copy_test")
  let cnt := (check[0]!.get (α := Int) 0 0).toOption.getD 0
  let sum := (check[0]!.get (α := Int) 0 1).toOption.getD 0
  if cnt != rows || sum != rows * (rows - 1) / 2 then
    return some s!"count {cnt} sum {sum}"
  let linesOut ← IO.mkRef 0
  let tagOut ← ok! (← conn.copyOut "COPY copy_test TO STDOUT" (fun b => do
    linesOut.modify (· + (b.toList.filter (· == 10)).length)))
  conn.close
  if tagOut != s!"COPY {rows}" then
    return some s!"copy out tag {tagOut}"
  expectIs ((← linesOut.get) == rows) s!"copy out lines {← linesOut.get}"

def listenNotify (ctx : Ctx) : IO (Option String) := do
  let listener ← connectUri ctx.url
  let sender ← connectUri ctx.url
  let _ ← ok! (← listener.listen "pg_lean_events")
  let _ ← ok! (← sender.notify "pg_lean_events" "payload-1")
  let n1 ← ok! (← listener.waitNotification 5000)
  let r ← match n1 with
    | some n =>
      if n.channel == "pg_lean_events" && n.payload == "payload-1" then
        let _ ← ok! (← sender.notify "pg_lean_events" "")
        match ← ok! (← listener.waitNotification 5000) with
        | some n2 => expectIs (n2.payload == "") s!"second payload {n2.payload}"
        | none => pure (some "second notification timed out")
      else
        pure (some s!"channel {n.channel} payload {n.payload}")
    | none => pure (some "notification timed out")
  listener.close
  sender.close
  pure r

def cancelSleep (ctx : Ctx) : IO (Option String) := do
  let conn ← connectUri ctx.url
  let task ← IO.asTask (conn.query "SELECT pg_sleep(30)")
  IO.sleep 500
  conn.cancel
  let outcome := task.get
  let r ← match outcome with
    | .error e => pure (some s!"task error {e}")
    | .ok (.error (.server fields)) =>
      expectIs (fields.sqlState? == some "57014")
        s!"sqlstate {fields.sqlState?.getD "?"}"
    | .ok (.error e) => pure (some s!"unexpected error {toString e}")
    | .ok (.ok _) => pure (some "query completed despite cancel")
  match ← conn.query "SELECT 1" with
  | .ok _ =>
    conn.close
    pure r
  | .error e =>
    conn.close
    pure (some s!"connection unusable after cancel: {toString e}")

def extendedPrepare (ctx : Ctx) : IO (Option String) := do
  let conn ← connectUri ctx.url
  let stmt ← ok! (← conn.prepare "st" "SELECT $1::int4 + $2::int4 AS total")
  let r ←
    if stmt.paramTypes != #[23, 23] then
      pure (some s!"param oids {stmt.paramTypes}")
    else if stmt.columns.map (·.name) != #["total"] then
      pure (some "column metadata")
    else
      match ← conn.execute "st" #[some "40".toUTF8, some "2".toUTF8] with
      | .error e => pure (some (toString e))
      | .ok rows =>
        expectIs (okEq (rows.get (α := Int) 0 0) 42 && rows.tag == "SELECT 1")
          s!"result {repr rows.rows}"
  conn.close
  pure r

def portalSuspend (ctx : Ctx) : IO (Option String) := do
  let conn ← connectUri ctx.url
  let _ ← ok! (← conn.exec "BEGIN")
  let events ← ok! (← conn.run #[
    .parse "" "SELECT generate_series(1, 5)",
    .bind "cur" "",
    .execute "cur" 2,
    .sync])
  let r ←
    if !events.any (· matches .portalSuspended) then
      pure (some "no PortalSuspended after row-limited Execute")
    else do
      let rest ← ok! (← conn.run #[.execute "cur" 0, .closePortal "cur", .sync])
      let rows := rest.filterMap fun
        | .dataRow cols => some cols
        | _ => none
      expectIs (rows.size == 3 && rest.any (· matches .closeComplete))
        s!"resume yielded {rows.size} rows"
  let _ ← ok! (← conn.exec "COMMIT")
  conn.close
  pure r

def codecParamRoundtrip (ctx : Ctx) : IO (Option String) := do
  let conn ← connectUri ctx.url
  let bad ← IO.mkRef (#[] : Array String)
  let roundtrip (α : Type) [PgDecode α] [PgEncode α] (cast : String) (x : α) : IO Unit := do
    let fmt := PgEncode.format α
    let bytes := PgEncode.encode x
    let record (why : String) : IO Unit := bad.modify (·.push s!"{cast}: {why}")
    match ← conn.prepare "" s!"SELECT $1::{cast} AS v" with
    | .error e => record (toString e)
    | .ok _ =>
      match ← conn.execute "" #[bytes] #[fmt] #[1] with
      | .error e => record (toString e)
      | .ok rows =>
        match rows.get (α := α) 0 0 with
        | .error e => record s!"decode: {e}"
        | .ok y =>
          let hx := (PgEncode.encode x).map Crypto.toHexLower
          let hy := (PgEncode.encode y).map Crypto.toHexLower
          unless hx == hy do
            record s!"sent {hx.getD "-"} got back {hy.getD "-"}"
  roundtrip Int "int8" 9007199254740993
  roundtrip Int "int4" (-42)
  roundtrip Float "float8" 1.5
  roundtrip Bool "bool" true
  roundtrip String "text" "héllo — 世界"
  roundtrip ByteArray "bytea" ((Crypto.ofHex? "deadbeef00ff").getD ByteArray.empty)
  roundtrip Std.Time.PlainDate "date"
    (Std.Time.PlainDate.ofDaysSinceUNIXEpoch (uv (8780 + pgEpochDays)))
  roundtrip Std.Time.PlainTime "time" (Std.Time.PlainTime.ofNanoseconds (uv 47045500000000))
  roundtrip Std.Time.PlainDateTime "timestamp" (dateTimeOfPgMicros 758966400000000)
  roundtrip Std.Time.Timestamp "timestamptz"
    (Std.Time.Timestamp.ofNanosecondsSinceUnixEpoch (uv ((pgEpochSeconds + 987) * 1000000000)))
  match PgNumeric.fromString "12345.678" with
  | .ok n => roundtrip PgNumeric "numeric" n
  | .error e => bad.modify (·.push s!"numeric fixture: {e}")
  roundtrip PgInterval "interval" ⟨14, 3, 14706789000⟩
  conn.close
  let failures ← bad.get
  expectIs failures.isEmpty (String.intercalate "; " failures.toList)

def pipelineMidError (ctx : Ctx) : IO (Option String) := do
  let conn ← connectUri ctx.url
  let events ← ok! (← conn.run #[
    .parse "pa" "SELECT 1",
    .bind "" "pa", .execute "" 0, .sync,
    .parse "pb" "SELECT * FROM nonexistent_table_xyz",
    .bind "" "pb", .execute "" 0, .sync,
    .parse "pc" "SELECT 3",
    .bind "" "pc", .execute "" 0, .sync])
  conn.close
  let readies := readyStatuses events
  let errors := serverErrors events
  let parses := (events.filter (· matches .parseComplete)).size
  expectIs (readies.size == 3 && errors.size == 1 &&
      (errors[0]!.sqlState? == some "42P01") && parses == 2)
    s!"readies {readies.size} errors {errors.size} parses {parses}"

def txStatusTracking (ctx : Ctx) : IO (Option String) := do
  let conn ← connectUri ctx.url
  let lastTx (events : Array Machine.Event) : Option TxStatus :=
    (readyStatuses events)[0]?
  let e1 ← ok! (← conn.run #[.simpleQuery "BEGIN"])
  let e2 ← ok! (← conn.run #[.simpleQuery "SELECT 1/0"])
  let e3 ← ok! (← conn.run #[.simpleQuery "ROLLBACK"])
  conn.close
  expectIs (lastTx e1 == some .inTransaction && lastTx e2 == some .failed &&
      lastTx e3 == some .idle && (serverErrors e2)[0]?.bind (·.sqlState?) == some "22012")
    s!"tx {repr (lastTx e1)} {repr (lastTx e2)} {repr (lastTx e3)}"

def bigRow (ctx : Ctx) : IO (Option String) := do
  let conn ← connectUri ctx.url
  let n := 10 * 1024 * 1024
  let rows ← ok! (← conn.query s!"SELECT repeat('x', {n}) AS big")
  conn.close
  match rows[0]!.get (α := String) 0 0 with
  | .ok s => expectIs (s.length == n) s!"length {s.length}"
  | .error e => pure (some e)

def unicodeRoundtrip (ctx : Ctx) : IO (Option String) := do
  let conn ← connectUri ctx.url
  let _ ← ok! (← conn.exec "CREATE TEMP TABLE データ (名前 text)")
  let _ ← ok! (← conn.exec "INSERT INTO データ VALUES ('héllo🐘')")
  let rows ← ok! (← conn.query "SELECT 名前 FROM データ")
  let encoding ← conn.parameter? "server_encoding"
  conn.close
  let r := rows[0]!.getByName (α := String) 0 "名前"
  expectIs (okEq r "héllo🐘" && encoding != some "SQL_ASCII") s!"got {repr r}"

def errorFieldCompleteness (ctx : Ctx) : IO (Option String) := do
  let conn ← connectUri ctx.url
  let _ ← ok! (← conn.exec "CREATE TEMP TABLE dup_test (id int4 PRIMARY KEY)")
  let _ ← ok! (← conn.exec "INSERT INTO dup_test VALUES (1)")
  let r ← match ← conn.exec "INSERT INTO dup_test VALUES (1)" with
    | .error (.server fields) =>
      expectIs (fields.sqlState? == some "23505" && fields.constraintName?.isSome &&
          fields.tableName? == some "dup_test" && fields.schemaName?.isSome &&
          fields.detail?.isSome && fields.severityCode? == some "ERROR")
        s!"fields {repr fields.fields}"
    | other => pure (some s!"expected unique violation, got ok={other matches .ok _}")
  conn.close
  pure r

def noticeDelivery (ctx : Ctx) : IO (Option String) := do
  let collected ← IO.mkRef (#[] : Array String)
  let conn ← connectUri ctx.url (onNotice := fun fields =>
    collected.modify (·.push (fields.message?.getD "")))
  let _ ← ok! (← conn.exec "DO $$ BEGIN RAISE NOTICE 'pg-lean says hi'; END $$")
  conn.close
  expectIs ((← collected.get).contains "pg-lean says hi")
    s!"notices {repr (← collected.get)}"

def simpleShapes (ctx : Ctx) : IO (Option String) := do
  let conn ← connectUri ctx.url
  let empty ← ok! (← conn.query "")
  let multi ← ok! (← conn.query "SELECT 1 AS a; SELECT 2 AS b, 3 AS c")
  conn.close
  expectIs (empty.map (·.tag) == #["EMPTY"] && multi.size == 2 &&
      okEq (multi[1]!.get (α := Int) 0 1) 3)
    s!"empty {repr (empty.map (·.tag))} multi {multi.size}"

def transportSecurity (ctx : Ctx) : IO (Option String) := do
  let cfg ← match ConnectConfig.parseUri ctx.url with
    | .ok cfg => pure cfg
    | .error e => return some s!"url: {e}"
  let conn ← connect cfg
  let localTls := conn.usesTls
  let certificate := ← conn.peerCertificate?
  let rows ← ok! (← conn.query
    "SELECT ssl::text FROM pg_stat_ssl WHERE pid = pg_backend_pid()")
  let serverTls := (rows[0]!.get (α := String) 0 0).toOption == some "true"
  conn.close
  if localTls != serverTls then
    pure (some s!"client TLS={localTls}, pg_stat_ssl={serverTls}")
  else if localTls && certificate.isNone then
    pure (some "TLS connection did not expose the server leaf certificate")
  else if cfg.sslMode == .require && !localTls then
    pure (some "sslmode=require connected without TLS")
  else if cfg.sslMode == .disable && localTls then
    pure (some "sslmode=disable unexpectedly used TLS")
  else
    pure none

def protocolNegotiation (ctx : Ctx) : IO (Option String) := do
  let cfg ← match ConnectConfig.parseUri ctx.url with
    | .ok cfg => pure cfg
    | .error e => return some s!"url: {e}"
  let conn ← connect { cfg with requestedVersion := .v3_2 }
  let version ← conn.protocolVersion
  let server := (← conn.parameter? "server_version").getD "?"
  let keySize := (conn.cancelKey.map (·.secret.size)).getD 0
  let modern := !(server.startsWith "17") && !(server.startsWith "16") &&
    !(server.startsWith "15") && !(server.startsWith "14")
  let r ←
    if modern then
      -- PG 18+: 3.2 accepted, variable-length cancel key
      if version != .v3_2 then pure (some s!"expected 3.2, got {repr version}")
      else if keySize ≤ 4 then pure (some s!"expected long cancel key, got {keySize}")
      else do
        -- cancellation must work with the long key
        let task ← IO.asTask (conn.query "SELECT pg_sleep(30)")
        IO.sleep 500
        conn.cancel
        match task.get with
        | .ok (.error (.server fields)) =>
          expectIs (fields.sqlState? == some "57014") "3.2 cancel sqlstate"
        | _ => pure (some "3.2 cancel did not interrupt")
    else
      -- pre-18 servers negotiate down to 3.0 with a 4-byte key
      expectIs (version == .v3_0 && keySize == 4)
        s!"expected downgrade to 3.0/4-byte key, got {repr version}/{keySize}"
  let alive ← conn.query "SELECT 1"
  conn.close
  match alive with
  | .ok _ => pure r
  | .error e => pure (some s!"connection dead after negotiation: {toString e}")

def runChecklist : IO UInt32 := do
  let some url ← IO.getEnv "PG_URL"
    | do
      IO.eprintln "PG_URL not set (postgres://user[:pass]@host:port/db)"
      return 2
  let ctx : Ctx := { url, failures := ← IO.mkRef 0 }
  let probe ← connectUri url
  IO.println s!"live checklist against {url} (server {(← probe.parameter? "server_version").getD "?"})"
  probe.close
  item ctx "transport.sslmode" (transportSecurity ctx)
  item ctx "simple.shapes" (simpleShapes ctx)
  item ctx "extended.prepare_describe" (extendedPrepare ctx)
  item ctx "extended.portal_suspend" (portalSuspend ctx)
  item ctx "codec.param_roundtrip" (codecParamRoundtrip ctx)
  item ctx "pipeline.mid_error" (pipelineMidError ctx)
  item ctx "tx.status_tracking" (txStatusTracking ctx)
  item ctx "errors.field_completeness" (errorFieldCompleteness ctx)
  item ctx "notices.raise_notice" (noticeDelivery ctx)
  item ctx "unicode.identifiers_data" (unicodeRoundtrip ctx)
  item ctx "bigrow.10mb" (bigRow ctx)
  item ctx "copy.roundtrip_100k" (copyRoundtrip ctx)
  item ctx "notify.cross_connection" (listenNotify ctx)
  item ctx "cancel.pg_sleep" (cancelSleep ctx)
  item ctx "protocol.negotiate_3_2" (protocolNegotiation ctx)
  let failures ← ctx.failures.get
  if failures == 0 then
    IO.println "ALL PASS"
    return 0
  else
    IO.println s!"{failures} FAILURE(S)"
    return 1

def connectOnly (url : String) : IO UInt32 := do
  try
    let conn ← connectUri url
    match ← conn.query "SELECT 1" with
    | .ok _ =>
      conn.close
      IO.println "CONNECT PASS"
      return (0 : UInt32)
    | .error e =>
      conn.close
      IO.eprintln s!"CONNECT FAIL: {e}"
      return (1 : UInt32)
  catch e =>
    IO.eprintln s!"CONNECT FAIL: {e}"
    return (1 : UInt32)

def connectExpectMechanism (url expected : String) : IO UInt32 := do
  try
    let conn ← connectUri url
    let actual ← conn.negotiatedSaslMechanism?
    if actual != some expected then
      conn.close
      IO.eprintln s!"CONNECT FAIL: expected SASL mechanism {expected}, got {repr actual}"
      return (1 : UInt32)
    match ← conn.query "SELECT 1" with
    | .ok _ =>
      conn.close
      IO.println s!"CONNECT PASS mechanism={expected}"
      return (0 : UInt32)
    | .error e =>
      conn.close
      IO.eprintln s!"CONNECT FAIL: {e}"
      return (1 : UInt32)
  catch e =>
    IO.eprintln s!"CONNECT FAIL: {e}"
    return (1 : UInt32)

def main (args : List String) : IO UInt32 := do
  match args with
  | [] => runChecklist
  | ["--connect", url] => connectOnly url
  | ["--connect-expect-mechanism", url, mechanism] =>
    connectExpectMechanism url mechanism
  | _ =>
    IO.eprintln
      "usage: pg_live_test [--connect URL | --connect-expect-mechanism URL MECHANISM]"
    return (2 : UInt32)
