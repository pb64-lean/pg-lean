import Pg.Connection
import Pg.Config
import Pg.Crypto.Hex

/-!
`pg_lean` — the command-line query client, a minimal non-interactive psql
built on the pg-lean library. It accepts any supported connection URL (auth
modes, `sslmode`/`sslrootcert`, `protocol=3.2`, ...) and runs one-shot
statements:

  pg_lean <postgres://url> SQL [SQL ...]        simple query protocol
  pg_lean -e <postgres://url> SQL [param ...]   prepared statement (\N = NULL)
  pg_lean -e -b <postgres://url> SQL [param ...] ... with binary-format
                                                results, rendered through the
                                                typed codecs

During development, run it from the build:

  bazel run //Cmd:pg_lean -- postgres://bill@localhost:5432/postgres "SELECT version()"
-/

open Pg
open Std.Async

def renderValue : Option ByteArray → String
  | none => "NULL"
  | some bytes =>
    match String.fromUTF8? bytes with
    | some s => s
    | none => "\\x" ++ Crypto.toHexLower bytes

def printRows (rs : Rows) : IO Unit := do
  unless rs.columns.isEmpty do
    IO.println (String.intercalate " | " (rs.columns.map (·.name)).toList)
    IO.println (String.intercalate "-+-" (rs.columns.map (fun c =>
      String.ofList (List.replicate c.name.length '-'))).toList)
    for row in rs.rows do
      IO.println (String.intercalate " | " (row.map renderValue).toList)
  IO.println s!"({rs.tag})"

def noticePrinter (fields : Pg.Protocol.ErrorFields) : IO Unit := do
  let sev := fields.severity?.getD "NOTICE"
  let msg := fields.message?.getD ""
  IO.eprintln s!"{sev}: {msg}"

/-- Render a cell through the typed codecs (decode by column OID/format,
re-encode as text) — exercises the real decoder paths, in both wire formats. -/
def renderTyped (cd : Pg.Protocol.ColumnDesc) (v : Option ByteArray) : String :=
  let rt (α : Type) [PgDecode α] [PgEncode α] : String :=
    match decodeValue (α := α) cd.typeOid cd.format v with
    | .ok x =>
      match PgEncode.encode x with
      | some b => (String.fromUTF8? b).getD ("\\x" ++ Crypto.toHexLower b)
      | none => "NULL"
    | .error e => s!"<decode error: {e}>"
  let rtArr (α : Type) [PgDecode α] [PgEncode α] [ToString α] : String :=
    match decodeValue (α := Array (Option α)) cd.typeOid cd.format v with
    | .ok xs =>
      let parts := xs.map fun
        | none => "NULL"
        | some x => toString x
      "{" ++ String.intercalate "," parts.toList ++ "}"
    | .error e => s!"<decode error: {e}>"
  if v.isNone then "NULL"
  else
    let oid := cd.typeOid
    if oid == Oid.bool then rt Bool
    else if #[Oid.int2, Oid.int4, Oid.int8, Oid.oid].contains oid then rt Int
    else if oid == Oid.float4 || oid == Oid.float8 then rt Float
    else if oid == Oid.bytea then
      match decodeValue (α := ByteArray) oid cd.format v with
      | .ok b => "\\x" ++ Crypto.toHexLower b
      | .error e => s!"<decode error: {e}>"
    else if oid == Oid.date then rt Std.Time.PlainDate
    else if oid == Oid.time then rt Std.Time.PlainTime
    else if oid == Oid.timestamp then rt Std.Time.PlainDateTime
    else if oid == Oid.timestamptz then rt Std.Time.Timestamp
    else if oid == Oid.interval then rt PgInterval
    else if oid == Oid.numeric then rt PgNumeric
    else if #[Oid.int2Array, Oid.int4Array, Oid.int8Array].contains oid then rtArr Int
    else if oid == Oid.float4Array || oid == Oid.float8Array then rtArr Float
    else if #[Oid.text, Oid.varchar, Oid.bpchar, Oid.name, Oid.char, Oid.json,
              Oid.jsonb, Oid.uuid].contains oid then rt String
    else if Oid.arrayElem oid != 0 then rtArr String
    else rt String

def printRowsTyped (rs : Rows) : IO Unit := do
  unless rs.columns.isEmpty do
    IO.println (String.intercalate " | " (rs.columns.map
      (fun c => s!"{c.name}[{c.typeOid}]")).toList)
    for row in rs.rows do
      let cells := (rs.columns.zip row).map (fun (cd, v) => renderTyped cd v)
      IO.println (String.intercalate " | " cells.toList)
  IO.println s!"({rs.tag})"

/-- Extended-protocol mode: prepared statement with text parameters
(`\N` = NULL): `pg_lean -e URL "SELECT $1::int + $2::int" 40 2`.
With `-b`, results are requested in binary format and rendered through the
typed codecs. -/
def runExtended (url sql : String) (params : List String) (binary : Bool := false) :
    Async UInt32 := do
  let cfg ← match ConnectConfig.parseUri url with
    | .ok cfg => pure cfg
    | .error e => IO.eprintln s!"bad url: {e}"; return 2
  let conn ← connect cfg (onNotice := noticePrinter)
  let stmt ← match ← conn.prepare "probe" sql with
    | .ok stmt => pure stmt
    | .error e => IO.eprintln (toString e); conn.close; return 1
  IO.eprintln s!"prepared: {stmt.paramTypes.size} parameter(s), {stmt.columns.size} column(s)"
  let wireParams := params.toArray.map (fun p =>
    if p == "\\N" then none else some p.toUTF8)
  match ← conn.execute "probe" wireParams (resultFormats := if binary then #[1] else #[]) with
  | .ok rows =>
    printRowsTyped rows
    conn.close
    return 0
  | .error e =>
    IO.eprintln (toString e)
    conn.close
    return 1

private def asyncMain (args : List String) : Async UInt32 := do
  match args with
  | "-e" :: "-b" :: url :: sql :: params => runExtended url sql params (binary := true)
  | "-e" :: url :: sql :: params => runExtended url sql params
  | url :: sql :: sqls => do
    let cfg ← match ConnectConfig.parseUri url with
      | .ok cfg => pure cfg
      | .error e => IO.eprintln s!"bad url: {e}"; return 2
    let conn ← connect cfg (onNotice := noticePrinter)
    let version ← conn.parameter? "server_version"
    IO.eprintln s!"connected (server {version.getD "?"})"
    let mut code : UInt32 := 0
    for stmt in sql :: sqls do
      IO.println s!"=> {stmt}"
      match ← conn.query stmt with
      | .ok results =>
        for rs in results do
          printRows rs
      | .error e =>
        IO.eprintln (toString e)
        code := 1
    conn.close
    return code
  | _ => do
    IO.eprintln "usage: pg_lean [-e [-b]] <postgres://user[:pass]@host[:port]/db> SQL [SQL|param ...]"
    return 2

def main (args : List String) : IO UInt32 :=
  Async.block (asyncMain args)
