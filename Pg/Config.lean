module

public import Pg.Protocol.Machine

public section

namespace Pg

/-- TLS negotiation policy, matching libpq's six `sslmode` values.

`verifyCa` and `verifyFull` are represented separately so callers cannot
accidentally lose their requested certificate-verification policy while the
connection layer decides which modes it can support. -/
inductive SslMode where
  | disable
  | allow
  | prefer
  | require
  | verifyCa
  | verifyFull
  deriving Repr, BEq, Inhabited

structure ConnectConfig where
  host : String := "localhost"
  port : UInt16 := 5432
  user : String := ""
  password : Option String := none
  database : Option String := none
  /-- Extra startup parameters (application_name, search_path, ...). -/
  parameters : Array (String × String) := #[]
  requestedVersion : Protocol.Machine.ProtocolVersion := .v3_0
  /-- TLS negotiation policy. Plaintext remains the default for backwards
  compatibility with pg-lean releases that predate TLS support. -/
  sslMode : SslMode := .disable
  /-- Optional PEM trust bundle used by `verify-ca` and `verify-full`.

  When absent, trust-store resolution consults `PGSSLROOTCERT` and then
  `~/.postgresql/root.crt`. Non-verifying TLS modes ignore this value. -/
  sslRootCert : Option System.FilePath := none
  /-- SCRAM channel-binding policy. `prefer` uses PLUS whenever a TLS server
  advertises it, `require` fails closed without PLUS, and `disable` always
  uses ordinary SCRAM-SHA-256. -/
  channelBinding : ChannelBindingMode := .prefer
  /-- Socket connect + startup handshake budget; 0 disables. -/
  connectTimeoutMs : Nat := 15000
  deriving Repr, Inhabited

namespace ConnectConfig

private def hexVal? (b : UInt8) : Option UInt8 :=
  if b ≥ 48 && b ≤ 57 then some (b - 48)
  else if b ≥ 97 && b ≤ 102 then some (b - 87)
  else if b ≥ 65 && b ≤ 70 then some (b - 55)
  else none

private def utf8Sub (raw : ByteArray) (lo hi : Nat) : String :=
  (String.fromUTF8? (raw.extract lo hi)).getD ""

/-- Split at the first occurrence of an ASCII delimiter (safe under UTF-8:
continuation bytes are ≥ 0x80). -/
private def splitFirst (s : String) (c : UInt8) : Option (String × String) := Id.run do
  let raw := s.toUTF8
  for i in [0:raw.size] do
    if raw.get! i == c then
      return some (utf8Sub raw 0 i, utf8Sub raw (i + 1) raw.size)
  return none

private def splitLast (s : String) (c : UInt8) : Option (String × String) := Id.run do
  let raw := s.toUTF8
  for k in [0:raw.size] do
    let i := raw.size - 1 - k
    if raw.get! i == c then
      return some (utf8Sub raw 0 i, utf8Sub raw (i + 1) raw.size)
  return none

private def afterPrefix (s prefix' : String) : Option String :=
  if s.startsWith prefix' then
    let raw := s.toUTF8
    some (utf8Sub raw prefix'.toUTF8.size raw.size)
  else none

def percentDecode (s : String) : String := Id.run do
  let raw := s.toUTF8
  let mut out := ByteArray.empty
  let mut i := 0
  while i < raw.size do
    let b := raw.get! i
    if b == 37 && i + 2 < raw.size then  -- '%'
      match hexVal? (raw.get! (i + 1)), hexVal? (raw.get! (i + 2)) with
      | some hi, some lo =>
        out := out.push (hi <<< 4 ||| lo)
        i := i + 3
      | _, _ =>
        out := out.push b
        i := i + 1
    else
      out := out.push b
      i := i + 1
  (String.fromUTF8? out).getD s

private def parsePort (s : String) : Except String UInt16 := do
  let some n := s.toNat? | throw s!"invalid port {s}"
  unless n > 0 && n ≤ 65535 do throw s!"invalid port {s}"
  pure (UInt16.ofNat n)

private def applyQueryParam (cfg : ConnectConfig) (key value : String) :
    Except String ConnectConfig := do
  match key with
  | "user" => pure { cfg with user := value }
  | "password" => pure { cfg with password := some value }
  | "dbname" => pure { cfg with database := some value }
  | "host" => pure { cfg with host := value }
  | "port" => do pure { cfg with port := ← parsePort value }
  | "sslrootcert" =>
    pure { cfg with sslRootCert := some (value : System.FilePath) }
  | "sslmode" =>
    match value with
    | "disable" => pure { cfg with sslMode := .disable }
    | "allow" => pure { cfg with sslMode := .allow }
    | "prefer" => pure { cfg with sslMode := .prefer }
    | "require" => pure { cfg with sslMode := .require }
    | "verify-ca" => pure { cfg with sslMode := .verifyCa }
    | "verify-full" => pure { cfg with sslMode := .verifyFull }
    | _ => throw s!"unknown sslmode {value} (disable, allow, prefer, require, verify-ca, or verify-full)"
  | "channel_binding" =>
    match value with
    | "prefer" => pure { cfg with channelBinding := .prefer }
    | "require" => pure { cfg with channelBinding := .require }
    | "disable" => pure { cfg with channelBinding := .disable }
    | _ => throw s!"unknown channel_binding {value} (prefer, require, or disable)"
  | "connect_timeout" => do
    let some secs := value.toNat? | throw s!"bad connect_timeout {value}"
    pure { cfg with connectTimeoutMs := secs * 1000 }
  | "protocol" =>
    match value with
    | "3.0" => pure { cfg with requestedVersion := .v3_0 }
    | "3.2" => pure { cfg with requestedVersion := .v3_2 }
    | _ => throw s!"unknown protocol version {value} (3.0 or 3.2)"
  | _ => pure { cfg with parameters := cfg.parameters.push (key, value) }

/-- `postgres://user[:password]@host[:port][/dbname][?key=value&...]`.

Subset of libpq's syntax: single host, no IPv6 bracket literals, no unix
sockets. Recognized query keys: user, password, dbname, host, port, sslmode
(disable/allow/prefer/require/verify-ca/verify-full), sslrootcert, and
channel_binding (prefer/require/disable);
everything else becomes a startup parameter. -/
def parseUri (uri : String) : Except String ConnectConfig := do
  let some rest := (afterPrefix uri "postgresql://").orElse (fun _ => afterPrefix uri "postgres://")
    | throw "URL must start with postgres:// or postgresql://"
  let (beforeQuery, query?) := match splitFirst rest 63 with  -- '?'
    | some (b, q) => (b, some q)
    | none => (rest, none)
  let (authority, path?) := match splitFirst beforeQuery 47 with  -- '/'
    | some (a, p) => (a, some p)
    | none => (beforeQuery, none)
  let (userinfo?, hostport) := match splitLast authority 64 with  -- '@'
    | some (u, hp) => (some u, hp)
    | none => (none, authority)
  let mut cfg : ConnectConfig := {}
  if let some userinfo := userinfo? then
    match splitFirst userinfo 58 with  -- ':'
    | some (u, pw) => cfg := { cfg with user := percentDecode u, password := some (percentDecode pw) }
    | none => cfg := { cfg with user := percentDecode userinfo }
  if hostport.startsWith "[" then
    throw "IPv6 bracket literals are not supported"
  match splitLast hostport 58 with  -- ':'
  | some (h, p) =>
    cfg := { cfg with port := ← parsePort p }
    if !h.isEmpty then cfg := { cfg with host := h }
  | none =>
    if !hostport.isEmpty then cfg := { cfg with host := hostport }
  if let some path := path? then
    let db := percentDecode path
    if !db.isEmpty then cfg := { cfg with database := some db }
  if let some query := query? then
    for pair in query.splitOn "&" do
      if pair.isEmpty then continue
      match splitFirst pair 61 with  -- '='
      | some (k, v) => cfg ← applyQueryParam cfg (percentDecode k) (percentDecode v)
      | none => throw s!"malformed query parameter {pair}"
  if cfg.user.isEmpty then
    throw "no user in URL (postgres://user@host/db)"
  pure cfg

end ConnectConfig

end Pg
