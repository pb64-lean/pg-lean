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

/-- What a connection must achieve before any application byte flows, decided
by `sslmode` alone.

* `requireEncryption` — a plaintext transport is never acceptable.
* `requireChain` — the server certificate must chain to a configured trust
  anchor, with every certificate inside its validity window
  (`TLS13.X509.Chain.validate` checks both).
* `requireHostname` — the chained leaf must additionally match the connection
  host (`TLS13.X509.Hostname.verifyHostname`).
* `allowsFallback` — the connection may retry with a different transport when
  the server rejects the first attempt.
-/
structure TlsPolicy where
  requireEncryption : Bool
  requireChain : Bool
  requireHostname : Bool
  allowsFallback : Bool
  deriving Repr, BEq, DecidableEq, Inhabited

/-- The single TLS decision table. `Connection.connect` (transport choice and
retry), `Connection.verifyTlsPeer` (chain + hostname), and
`Tls.TrustStore.verificationRequested` (trust-store loading) all read their
behaviour off this one function; the laws below pin down what each mode
guarantees. -/
@[expose] def SslMode.policy : SslMode → TlsPolicy
  | .disable =>
    { requireEncryption := false, requireChain := false,
      requireHostname := false, allowsFallback := false }
  | .allow =>
    { requireEncryption := false, requireChain := false,
      requireHostname := false, allowsFallback := true }
  | .prefer =>
    { requireEncryption := false, requireChain := false,
      requireHostname := false, allowsFallback := true }
  | .require =>
    { requireEncryption := true, requireChain := false,
      requireHostname := false, allowsFallback := false }
  | .verifyCa =>
    { requireEncryption := true, requireChain := true,
      requireHostname := false, allowsFallback := false }
  | .verifyFull =>
    { requireEncryption := true, requireChain := true,
      requireHostname := true, allowsFallback := false }

/-!
### TLS policy laws

Per-mode guarantees, and the coherence conditions that make the table safe:
a mode that checks identity also checks the chain, a mode that checks the
chain also demands encryption, and no mode that demands encryption is ever
allowed to retry in a weaker transport.
-/

/-- `verify-full` ⇒ encryption + chain (with validity time) + hostname. -/
theorem verifyFull_policy :
    SslMode.verifyFull.policy =
      { requireEncryption := true, requireChain := true,
        requireHostname := true, allowsFallback := false } := by rfl

/-- `verify-ca` ⇒ encryption + chain (with validity time), no host identity. -/
theorem verifyCa_policy :
    SslMode.verifyCa.policy =
      { requireEncryption := true, requireChain := true,
        requireHostname := false, allowsFallback := false } := by rfl

/-- `require` ⇒ encryption without any certificate identity check. -/
theorem require_policy :
    SslMode.require.policy =
      { requireEncryption := true, requireChain := false,
        requireHostname := false, allowsFallback := false } := by rfl

/-- Identity implies chain: hostname verification is never performed against
an unvalidated certificate. -/
theorem policy_hostname_implies_chain (m : SslMode) :
    (m.policy).requireHostname = true → (m.policy).requireChain = true := by
  intro h
  cases m <;> first | rfl | exact absurd h (by decide)

/-- Chain implies encryption: certificate validation is never claimed for a
plaintext transport. -/
theorem policy_chain_implies_encryption (m : SslMode) :
    (m.policy).requireChain = true → (m.policy).requireEncryption = true := by
  intro h
  cases m <;> first | rfl | exact absurd h (by decide)

/-- **No insecure fallback**: no mode that demands encryption is permitted to
retry in a weaker transport, so no failure path can silently downgrade. -/
theorem policy_no_insecure_fallback (m : SslMode) :
    (m.policy).requireEncryption = true → (m.policy).allowsFallback = false := by
  intro h
  cases m <;> first | rfl | exact absurd h (by decide)

/-- Only the two opportunistic modes may retry at all. -/
theorem policy_fallback_iff (m : SslMode) :
    (m.policy).allowsFallback = true ↔ (m = .allow ∨ m = .prefer) := by
  cases m <;>
    first
      | exact ⟨fun _ => Or.inl rfl, fun _ => rfl⟩
      | exact ⟨fun _ => Or.inr rfl, fun _ => rfl⟩
      | exact ⟨fun h => absurd h (by decide), fun h => by rcases h with h | h <;> cases h⟩

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

/-!
### Provable string surgery

Every split below goes through `List Char`. `String.splitOn` is a dead end for
proofs — `String.splitOnAux` is `@[irreducible]`, its `eq_def` is private to
core, and core 4.31 ships no lemmas about it — whereas `List` has a full set.
The delimiters a `postgres://` URI uses (`: @ / ? & = %`) are all ASCII and
UTF-8 continuation bytes are all `≥ 0x80`, so splitting on a `Char` is exactly
the byte split this parser performed before.
-/

private def splitFirstAux (c : Char) : List Char → Option (List Char × List Char)
  | [] => none
  | a :: rest =>
    if a == c then some ([], rest)
    else
      match splitFirstAux c rest with
      | some (pre, post) => some (a :: pre, post)
      | none => none

private def splitLastAux (c : Char) : List Char → Option (List Char × List Char)
  | [] => none
  | a :: rest =>
    match splitLastAux c rest with
    | some (pre, post) => some (a :: pre, post)
    | none => if a == c then some ([], rest) else none

/-- Split at the first occurrence of an ASCII delimiter. -/
def splitFirstChar (c : Char) (s : String) : Option (String × String) :=
  match splitFirstAux c s.toList with
  | some (pre, post) => some (String.ofList pre, String.ofList post)
  | none => none

/-- Split at the last occurrence of an ASCII delimiter. -/
def splitLastChar (c : Char) (s : String) : Option (String × String) :=
  match splitLastAux c s.toList with
  | some (pre, post) => some (String.ofList pre, String.ofList post)
  | none => none

private theorem splitFirstAux_length : ∀ {c : Char} {l pre post : List Char},
    splitFirstAux c l = some (pre, post) → post.length < l.length := by
  intro c l
  induction l with
  | nil => intro pre post h; cases h
  | cons a t ih =>
    intro pre post h
    unfold splitFirstAux at h
    split at h
    · cases h
      exact Nat.lt_succ_self _
    · split at h
      · next p q hq =>
        cases h
        exact Nat.lt_succ_of_lt (ih hq)
      · cases h

set_option linter.unusedVariables false in
private def splitAllAux (c : Char) (l : List Char) : List (List Char) :=
  match h : splitFirstAux c l with
  | some (pre, post) =>
    have hlt : post.length < l.length := splitFirstAux_length h
    pre :: splitAllAux c post
  | none => [l]
  termination_by l.length
  decreasing_by exact hlt

/-- Split into every field separated by an ASCII delimiter — the `&` of a URI
query string. Agrees with `String.splitOn` for a one-character separator. -/
def splitAllChar (c : Char) (s : String) : List String :=
  (splitAllAux c s.toList).map String.ofList

/-- Everything after a literal ASCII prefix, when the string carries it. -/
private def afterPrefix (s pre : String) : Option String :=
  if s.startsWith pre then
    some (String.ofList (s.toList.drop pre.toList.length))
  else none

/-!
### Percent-encoding

Decoding happens on UTF-8 *bytes*, not characters: `%C3%A4` is the two-byte
encoding of `ä`, so a character-level decoder would corrupt every non-ASCII
password or database name. `percentEncode` is the inverse (`percentDecode_percentEncode`),
escaping everything outside RFC 3986's unreserved set — which covers every
delimiter this parser splits on and every non-ASCII byte.
-/

/-- Bytes RFC 3986 leaves unescaped: ALPHA / DIGIT / `-` / `.` / `_` / `~`. -/
private def unreservedByte (b : UInt8) : Bool :=
  let v := b.toNat
  (48 ≤ v && v ≤ 57) || (65 ≤ v && v ≤ 90) || (97 ≤ v && v ≤ 122) ||
    v == 45 || v == 46 || v == 95 || v == 126

/-- Nibble value of an ASCII hex digit (upper or lower case). -/
private def hexVal? (b : UInt8) : Option Nat :=
  let v := b.toNat
  if 48 ≤ v && v ≤ 57 then some (v - 48)
  else if 97 ≤ v && v ≤ 102 then some (v - 87)
  else if 65 ≤ v && v ≤ 70 then some (v - 55)
  else none

/-- ASCII byte of a nibble, upper case (`0`-`9`, `A`-`F`). -/
private def hexDigitByte (n : Nat) : UInt8 :=
  if n < 10 then UInt8.ofNat (48 + n) else UInt8.ofNat (55 + n)

private def percentEncodeBytes : List UInt8 → List UInt8
  | [] => []
  | b :: rest =>
    if unreservedByte b then b :: percentEncodeBytes rest
    else 37 :: hexDigitByte (b.toNat / 16) :: hexDigitByte (b.toNat % 16) ::
      percentEncodeBytes rest

private def percentDecodeBytes : List UInt8 → List UInt8
  | b :: h :: l :: tail =>
    if b == 37 then
      match hexVal? h, hexVal? l with
      | some hi, some lo => UInt8.ofNat (hi * 16 + lo) :: percentDecodeBytes tail
      | _, _ => b :: percentDecodeBytes (h :: l :: tail)
    else b :: percentDecodeBytes (h :: l :: tail)
  | b :: rest => b :: percentDecodeBytes rest
  | [] => []
  termination_by xs => xs.length
  decreasing_by all_goals simp only [List.length_cons]; omega

private def asciiChars (l : List UInt8) : List Char :=
  l.map (fun b => Char.ofNat b.toNat)

/-- Percent-decode a URI component. Invalid escapes are left verbatim (libpq
does the same), and a decode that would not be valid UTF-8 yields the input
unchanged rather than a lossy string. -/
def percentDecode (s : String) : String :=
  (String.fromUTF8? (percentDecodeBytes s.toUTF8.data.toList).toByteArray).getD s

/-- Percent-encode a URI component: every byte outside RFC 3986's unreserved
set — every delimiter, and every byte of a non-ASCII character — becomes
`%XX`. `percentDecode_percentEncode` proves this is a faithful inverse. -/
def percentEncode (s : String) : String :=
  String.ofList (asciiChars (percentEncodeBytes s.toUTF8.data.toList))

private def parsePort (s : String) : Except String UInt16 :=
  match s.toNat? with
  | none => .error s!"invalid port {s}"
  | some n =>
    if 0 < n && n ≤ 65535 then .ok (UInt16.ofNat n) else .error s!"invalid port {s}"

/-- Interpret one `key=value` query parameter. Recognized keys set the
corresponding field; every other key becomes a startup parameter, which
`applyQueryParam_unknown` proves can neither fail nor disturb a recognized
setting. -/
def applyQueryParam (cfg : ConnectConfig) (key value : String) :
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

/-- The `user[:password]` part of the authority. -/
def applyUserInfo (cfg : ConnectConfig) (userinfo : String) : ConnectConfig :=
  match splitFirstChar ':' userinfo with
  | some (u, pw) =>
    { cfg with user := percentDecode u, password := some (percentDecode pw) }
  | none => { cfg with user := percentDecode userinfo }

/-- The `host[:port]` part of the authority. -/
def applyHostPort (cfg : ConnectConfig) (hostport : String) :
    Except String ConnectConfig :=
  if hostport.startsWith "[" then
    .error "IPv6 bracket literals are not supported"
  else
    match splitLastChar ':' hostport with
    | some (h, p) =>
      match parsePort p with
      | .error e => .error e
      | .ok port =>
        if h.isEmpty then .ok { cfg with port } else .ok { cfg with host := h, port }
    | none =>
      if hostport.isEmpty then .ok cfg else .ok { cfg with host := hostport }

/-- The `/dbname` part of the path. -/
def applyPath (cfg : ConnectConfig) (path : String) : ConnectConfig :=
  let db := percentDecode path
  if db.isEmpty then cfg else { cfg with database := some db }

/-- Fold the `&`-separated fields of a query string, left to right. Empty
fields are skipped (`?a=1&&b=2` is accepted, as libpq accepts it). -/
def applyQueryPairs (cfg : ConnectConfig) : List String → Except String ConnectConfig
  | [] => .ok cfg
  | field :: rest =>
    if field.isEmpty then applyQueryPairs cfg rest
    else
      match splitFirstChar '=' field with
      | some (k, v) =>
        match applyQueryParam cfg (percentDecode k) (percentDecode v) with
        | .error e => .error e
        | .ok cfg' => applyQueryPairs cfg' rest
      | none => .error s!"malformed query parameter {field}"

/-- `postgres://user[:password]@host[:port][/dbname][?key=value&...]`.

Subset of libpq's syntax: single host, no IPv6 bracket literals, no unix
sockets. Recognized query keys: user, password, dbname, host, port, sslmode
(disable/allow/prefer/require/verify-ca/verify-full), sslrootcert, and
channel_binding (prefer/require/disable);
everything else becomes a startup parameter.

Written as a pure `match` chain over the split helpers above (not a `do`
block with `let mut`) so `parseUri_renderUri` can evaluate it. -/
def parseUri (uri : String) : Except String ConnectConfig :=
  match (afterPrefix uri "postgresql://").orElse
      (fun _ => afterPrefix uri "postgres://") with
  | none => .error "URL must start with postgres:// or postgresql://"
  | some rest =>
    match splitFirstChar '?' rest with
    | some (beforeQuery, query) => parseAuthority beforeQuery (some query)
    | none => parseAuthority rest none
where
  /-- Everything after the scheme, with the query string already separated. -/
  parseAuthority (beforeQuery : String) (query? : Option String) :
      Except String ConnectConfig :=
    let (authority, path?) := match splitFirstChar '/' beforeQuery with
      | some (a, p) => (a, some p)
      | none => (beforeQuery, none)
    let (userinfo?, hostport) := match splitLastChar '@' authority with
      | some (u, hp) => (some u, hp)
      | none => (none, authority)
    let cfg0 : ConnectConfig := match userinfo? with
      | some userinfo => applyUserInfo {} userinfo
      | none => {}
    match applyHostPort cfg0 hostport with
    | .error e => .error e
    | .ok cfg1 =>
      let cfg2 := match path? with
        | some path => applyPath cfg1 path
        | none => cfg1
      match (match query? with
             | some query => applyQueryPairs cfg2 (splitAllChar '&' query)
             | none => .ok cfg2) with
      | .error e => .error e
      | .ok cfg3 =>
        if cfg3.user.isEmpty then
          .error "no user in URL (postgres://user@host/db)"
        else .ok cfg3

end ConnectConfig

end Pg
