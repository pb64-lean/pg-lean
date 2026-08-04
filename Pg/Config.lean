module

public import Std.Data.String
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
  (48 ≤ b.toNat && b.toNat ≤ 57) || (65 ≤ b.toNat && b.toNat ≤ 90) ||
    (97 ≤ b.toNat && b.toNat ≤ 122) ||
    b.toNat == 45 || b.toNat == 46 || b.toNat == 95 || b.toNat == 126

/-- Nibble value of an ASCII hex digit (upper or lower case). -/
private def hexVal? (b : UInt8) : Option Nat :=
  if 48 ≤ b.toNat && b.toNat ≤ 57 then some (b.toNat - 48)
  else if 97 ≤ b.toNat && b.toNat ≤ 102 then some (b.toNat - 87)
  else if 65 ≤ b.toNat && b.toNat ≤ 70 then some (b.toNat - 55)
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

/-- Apply the query string (when present) and enforce that a user was given. -/
private def finishUri (r : Except String ConnectConfig) (query? : Option String) :
    Except String ConnectConfig :=
  match r with
  | .error e => .error e
  | .ok cfg =>
    match (match query? with
           | some query => applyQueryPairs cfg (splitAllChar '&' query)
           | none => .ok cfg) with
    | .error e => .error e
    | .ok cfg' =>
      if cfg'.user.isEmpty then
        .error "no user in URL (postgres://user@host/db)"
      else .ok cfg'

/-- The `host[:port]` component, then the path and query. -/
private def parseHostPart (cfg0 : ConnectConfig) (hostport : String)
    (path? query? : Option String) : Except String ConnectConfig :=
  match applyHostPort cfg0 hostport with
  | .error e => .error e
  | .ok cfg1 =>
    match path? with
    | some path => finishUri (.ok (applyPath cfg1 path)) query?
    | none => finishUri (.ok cfg1) query?

/-- The authority, split at its last `@` into user info and `host[:port]`. -/
private def parseAuthority (authority : String) (path? query? : Option String) :
    Except String ConnectConfig :=
  match splitLastChar '@' authority with
  | some (userinfo, hostport) =>
    parseHostPart (applyUserInfo {} userinfo) hostport path? query?
  | none => parseHostPart {} authority path? query?

/-- Everything after the scheme, split at its first `/` into authority and
path. -/
private def parseAfterScheme (beforeQuery : String) (query? : Option String) :
    Except String ConnectConfig :=
  match splitFirstChar '/' beforeQuery with
  | some (authority, path) => parseAuthority authority (some path) query?
  | none => parseAuthority beforeQuery none query?

/-- `postgres://user[:password]@host[:port][/dbname][?key=value&...]`.

Subset of libpq's syntax: single host, no IPv6 bracket literals, no unix
sockets. Recognized query keys: user, password, dbname, host, port, sslmode
(disable/allow/prefer/require/verify-ca/verify-full), sslrootcert, and
channel_binding (prefer/require/disable);
everything else becomes a startup parameter.

Written as a chain of small pure `match`es over the split helpers above (not a
`do` block with `let mut`) so `parseUri_renderUri` can evaluate it. -/
def parseUri (uri : String) : Except String ConnectConfig :=
  match (afterPrefix uri "postgresql://").orElse
      (fun _ => afterPrefix uri "postgres://") with
  | none => .error "URL must start with postgres:// or postgresql://"
  | some rest =>
    match splitFirstChar '?' rest with
    | some (beforeQuery, query) => parseAfterScheme beforeQuery (some query)
    | none => parseAfterScheme rest none

/-!
### Percent-encoding laws
-/

private theorem toNat_ofNat_ascii {n : Nat} (h : n ≤ 127) :
    (Char.ofNat n).val.toNat = n := by
  unfold Char.ofNat
  rw [dif_pos (by unfold Nat.isValidChar; omega)]
  unfold Char.ofNatAux
  simp [UInt32.toNat]

private theorem utf8EncodeChar_ascii {b : UInt8} (h : b.toNat ≤ 127) :
    String.utf8EncodeChar (Char.ofNat b.toNat) = [b] := by
  unfold String.utf8EncodeChar
  rw [show (Char.ofNat b.toNat).val.toNat = b.toNat from toNat_ofNat_ascii h,
    if_pos h, UInt8.ofNat_toNat]

private theorem utf8Encode_asciiChars : ∀ {l : List UInt8}, (∀ b ∈ l, b.toNat ≤ 127) →
    (asciiChars l).utf8Encode = l.toByteArray := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons b t ih =>
    intro h
    have hb : b.toNat ≤ 127 := h b (List.mem_cons_self ..)
    show (Char.ofNat b.toNat :: asciiChars t).utf8Encode = _
    rw [List.utf8Encode_cons, List.utf8Encode_singleton, utf8EncodeChar_ascii hb,
      ih (fun x hx => h x (List.mem_cons_of_mem _ hx)),
      show (b :: t) = [b] ++ t from rfl, List.toByteArray_append]

private theorem toByteArray_data_toList (a : ByteArray) : a.data.toList.toByteArray = a := by
  have h : (a.data.toList.toByteArray).data = a.data := by
    rw [List.data_toByteArray, Array.toArray_toList]
  exact congrArg ByteArray.mk h

private theorem fromUTF8?_toUTF8 (s : String) : String.fromUTF8? s.toUTF8 = some s := by
  rw [String.toUTF8_eq_toByteArray]
  unfold String.fromUTF8?
  split
  · rfl
  · next h => exact absurd s.isValidUTF8 h

private theorem toNat_hexDigitByte {n : Nat} (h : n < 16) :
    (hexDigitByte n).toNat = if n < 10 then 48 + n else 55 + n := by
  unfold hexDigitByte
  split
  · rw [UInt8.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
  · rw [UInt8.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]

private theorem hexVal?_hexDigitByte {n : Nat} (h : n < 16) :
    hexVal? (hexDigitByte n) = some n := by
  have hb := toNat_hexDigitByte h
  unfold hexVal?
  rw [hb]
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  by_cases hn : n < 10
  · rw [if_pos hn, if_pos (by omega)]
    exact congrArg some (by omega)
  · rw [if_neg hn, if_neg (by omega), if_neg (by omega), if_pos (by omega)]
    exact congrArg some (by omega)

private theorem beq_37_eq_false {b : UInt8} (h : b.toNat ≠ 37) : (b == 37) = false :=
  beq_eq_false_iff_ne.mpr (fun hb => h (by rw [hb]; rfl))

private theorem hexDigitByte_safe {n : Nat} (h : n < 16) :
    (hexDigitByte n).toNat ≤ 127 ∧ (hexDigitByte n == 37) = false := by
  have hb := toNat_hexDigitByte h
  have hrange : 48 ≤ (hexDigitByte n).toNat ∧ (hexDigitByte n).toNat ≤ 70 := by
    split at hb <;> omega
  exact ⟨by omega, beq_37_eq_false (by omega)⟩

private theorem unreservedByte_safe {b : UInt8} (h : unreservedByte b = true) :
    b.toNat ≤ 127 ∧ (b == 37) = false := by
  unfold unreservedByte at h
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  exact ⟨by omega, beq_37_eq_false (by omega)⟩

private theorem percentEncodeBytes_ascii : ∀ {l : List UInt8} {b : UInt8},
    b ∈ percentEncodeBytes l → b.toNat ≤ 127 := by
  intro l
  induction l with
  | nil => intro b hb; cases hb
  | cons a t ih =>
    intro b hb
    have ha : a.toNat < 256 := UInt8.toNat_lt_size a
    unfold percentEncodeBytes at hb
    split at hb
    · rcases List.mem_cons.mp hb with rfl | hb
      · exact (unreservedByte_safe ‹_›).1
      · exact ih hb
    · rcases List.mem_cons.mp hb with rfl | hb
      · decide
      rcases List.mem_cons.mp hb with rfl | hb
      · exact (hexDigitByte_safe (by omega)).1
      rcases List.mem_cons.mp hb with rfl | hb
      · exact (hexDigitByte_safe (Nat.mod_lt _ (by omega))).1
      · exact ih hb

private theorem percentDecodeBytes_cons_ne {b : UInt8} (hb : (b == 37) = false)
    (rest : List UInt8) :
    percentDecodeBytes (b :: rest) = b :: percentDecodeBytes rest := by
  match rest with
  | [] => simp only [percentDecodeBytes]
  | [_] => simp only [percentDecodeBytes]
  | _ :: _ :: _ => simp only [percentDecodeBytes, hb, Bool.false_eq_true, if_false]

private theorem percentDecodeBytes_escape {d₁ d₂ : UInt8} {hi lo : Nat}
    {tail : List UInt8} (h₁ : hexVal? d₁ = some hi) (h₂ : hexVal? d₂ = some lo) :
    percentDecodeBytes (37 :: d₁ :: d₂ :: tail)
      = UInt8.ofNat (hi * 16 + lo) :: percentDecodeBytes tail := by
  simp only [percentDecodeBytes]
  rw [if_pos (show ((37 : UInt8) == 37) = true from rfl)]
  simp only [h₁, h₂]

/-- **Percent-encoding roundtrip**, at the byte level: every byte survives,
including the UTF-8 continuation bytes of a non-ASCII character. -/
private theorem percentDecodeBytes_percentEncodeBytes (l : List UInt8) :
    percentDecodeBytes (percentEncodeBytes l) = l := by
  induction l with
  | nil => simp only [percentEncodeBytes, percentDecodeBytes]
  | cons b t ih =>
    have hb : b.toNat < 256 := UInt8.toNat_lt_size b
    unfold percentEncodeBytes
    split
    · rw [percentDecodeBytes_cons_ne (unreservedByte_safe ‹_›).2, ih]
    · rw [percentDecodeBytes_escape (hexVal?_hexDigitByte (by omega))
        (hexVal?_hexDigitByte (Nat.mod_lt _ (by omega))), ih]
      refine congrArg (· :: t) ?_
      rw [show b.toNat / 16 * 16 + b.toNat % 16 = b.toNat from Nat.div_add_mod' _ _]
      exact UInt8.ofNat_toNat

/-- **Percent-decoding is a faithful inverse of percent-encoding** for every
string, non-ASCII included: `percentEncode` escapes each UTF-8 byte, so a
password such as `pg-lean-läuft` survives a URI roundtrip byte for byte. -/
theorem percentDecode_percentEncode (s : String) : percentDecode (percentEncode s) = s := by
  have henc : (percentEncode s).toUTF8
      = (percentEncodeBytes s.toUTF8.data.toList).toByteArray := by
    unfold percentEncode
    rw [String.toUTF8_eq_toByteArray,
      show (String.ofList (asciiChars (percentEncodeBytes s.toUTF8.data.toList))).toByteArray
        = (asciiChars (percentEncodeBytes s.toUTF8.data.toList)).utf8Encode from rfl]
    exact utf8Encode_asciiChars (fun _ hb => percentEncodeBytes_ascii hb)
  unfold percentDecode
  rw [henc, List.toList_data_toByteArray, percentDecodeBytes_percentEncodeBytes,
    toByteArray_data_toList, fromUTF8?_toUTF8]
  rfl

/-!
### URI render/parse roundtrip

`renderUri` is the inverse direction of `parseUri` for the components a URI
authority and path carry. `parseUri_renderUri` proves the roundtrip under
exactly the conditions a URI authority imposes: the host carries no delimiter
(everything else is percent-escaped), the port is non-zero, and the user and
database names are non-empty (an empty one is indistinguishable from an absent
one on the wire).
-/

/-- Characters that must not appear unescaped in a URI authority component:
the four delimiters `parseUri` splits on (`: @ / ?`), the two query separators
(`& =`), and `[`, the IPv6-literal marker it rejects. -/
@[expose] def uriSafeChar (c : Char) : Bool :=
  c.val.toNat != 58 && c.val.toNat != 64 && c.val.toNat != 47 &&
    c.val.toNat != 63 && c.val.toNat != 38 && c.val.toNat != 61 &&
    c.val.toNat != 91

private def userInfoChars (cfg : ConnectConfig) : List Char :=
  (percentEncode cfg.user).toList ++
    (match cfg.password with
     | some pw => ':' :: (percentEncode pw).toList
     | none => [])

private def hostPortChars (cfg : ConnectConfig) : List Char :=
  cfg.host.toList ++ ':' :: (Nat.repr cfg.port.toNat).toList

private def pathChars (cfg : ConnectConfig) : List Char :=
  match cfg.database with
  | some db => '/' :: (percentEncode db).toList
  | none => []

private def uriBody (cfg : ConnectConfig) : List Char :=
  userInfoChars cfg ++ '@' :: (hostPortChars cfg ++ pathChars cfg)

/-- `postgresql://user[:password]@host:port[/dbname]`, with every component
that can carry a delimiter percent-escaped. `parseUri_renderUri` proves
`parseUri` reads back exactly these components. -/
def renderUri (cfg : ConnectConfig) : String :=
  String.ofList ("postgresql://".toList ++ uriBody cfg)

/-! #### Character-set lemmas -/

private theorem ne_of_uriSafe {l : List Char} {d : Char}
    (hl : ∀ c ∈ l, uriSafeChar c = true) (hd : uriSafeChar d = false) :
    ∀ a ∈ l, a ≠ d := by
  intro a ha hne
  have h := hl a ha
  rw [hne, hd] at h
  cases h

private theorem ne_append {l₁ l₂ : List Char} {d : Char}
    (h₁ : ∀ a ∈ l₁, a ≠ d) (h₂ : ∀ a ∈ l₂, a ≠ d) : ∀ a ∈ l₁ ++ l₂, a ≠ d :=
  fun a ha => (List.mem_append.mp ha).elim (h₁ a) (h₂ a)

private theorem ne_cons {x : Char} {l : List Char} {d : Char}
    (hx : x ≠ d) (h : ∀ a ∈ l, a ≠ d) : ∀ a ∈ x :: l, a ≠ d :=
  fun a ha => (List.mem_cons.mp ha).elim (fun h' => h' ▸ hx) (h a)

private theorem uriSafeChar_ofNat {n : Nat} (h : n ≤ 127)
    (h58 : n ≠ 58) (h64 : n ≠ 64) (h47 : n ≠ 47) (h63 : n ≠ 63)
    (h38 : n ≠ 38) (h61 : n ≠ 61) (h91 : n ≠ 91) :
    uriSafeChar (Char.ofNat n) = true := by
  unfold uriSafeChar
  rw [toNat_ofNat_ascii h]
  simp only [bne_iff_ne, ne_eq, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨h58, h64⟩, h47⟩, h63⟩, h38⟩, h61⟩, h91⟩

private theorem percentEncodeBytes_range : ∀ {l : List UInt8} {b : UInt8},
    b ∈ percentEncodeBytes l →
      b.toNat = 37 ∨ (48 ≤ b.toNat ∧ b.toNat ≤ 57) ∨ (65 ≤ b.toNat ∧ b.toNat ≤ 90) ∨
        (97 ≤ b.toNat ∧ b.toNat ≤ 122) ∨ b.toNat = 45 ∨ b.toNat = 46 ∨
        b.toNat = 95 ∨ b.toNat = 126 := by
  intro l
  induction l with
  | nil => intro b hb; cases hb
  | cons a t ih =>
    intro b hb
    have ha : a.toNat < 256 := UInt8.toNat_lt_size a
    unfold percentEncodeBytes at hb
    split at hb
    · rcases List.mem_cons.mp hb with rfl | hb
      · rename_i hu
        unfold unreservedByte at hu
        simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hu
        omega
      · exact ih hb
    · rcases List.mem_cons.mp hb with rfl | hb
      · exact Or.inl rfl
      rcases List.mem_cons.mp hb with rfl | hb
      · have := toNat_hexDigitByte (n := a.toNat / 16) (by omega)
        split at this <;> omega
      rcases List.mem_cons.mp hb with rfl | hb
      · have := toNat_hexDigitByte (n := a.toNat % 16) (Nat.mod_lt _ (by omega))
        split at this <;> omega
      · exact ih hb

/-- Every character of a percent-encoded component is URI-safe: the escape
alphabet is `%`, the ASCII alphanumerics, and `- . _ ~`. -/
private theorem uriSafeChar_percentEncode (s : String) :
    ∀ c ∈ (percentEncode s).toList, uriSafeChar c = true := by
  intro c hc
  unfold percentEncode at hc
  rw [String.toList_ofList] at hc
  unfold asciiChars at hc
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hc
  have hr := percentEncodeBytes_range hb
  exact uriSafeChar_ofNat (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega)

private theorem uriSafeChar_of_isDigit {c : Char} (h : c.isDigit = true) :
    uriSafeChar c = true := by
  unfold Char.isDigit at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  have h1 : (48 : Nat) ≤ c.val.toNat := by
    have := UInt32.le_iff_toNat_le.mp h.1
    rw [show ('0'.val).toNat = 48 from by decide] at this
    exact this
  have h2 : c.val.toNat ≤ 57 := by
    have := UInt32.le_iff_toNat_le.mp h.2
    rw [show ('9'.val).toNat = 57 from by decide] at this
    exact this
  unfold uriSafeChar
  simp only [bne_iff_ne, ne_eq, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨by omega, by omega⟩, by omega⟩, by omega⟩, by omega⟩, by omega⟩, by omega⟩

/-- Every character of a decimal render is URI-safe: `String.isNat` pins them
to the digits (plus Lean's `_` separator, which is unreserved anyway). -/
private theorem uriSafeChar_repr (n : Nat) :
    ∀ c ∈ (Nat.repr n).toList, uriSafeChar c = true := by
  intro c hc
  obtain ⟨-, hdig, -⟩ := String.isNat_iff.mp (Nat.isNat_repr n)
  rcases hdig c hc with h | rfl
  · exact uriSafeChar_of_isDigit h
  · decide

/-! #### Split lemmas -/

private theorem splitFirstAux_append {c : Char} : ∀ {p : List Char} (q : List Char),
    (∀ a ∈ p, a ≠ c) → splitFirstAux c (p ++ c :: q) = some (p, q) := by
  intro p
  induction p with
  | nil =>
    intro q _
    rw [List.nil_append]
    unfold splitFirstAux
    rw [if_pos (beq_self_eq_true c)]
  | cons a t ih =>
    intro q h
    rw [List.cons_append]
    unfold splitFirstAux
    rw [if_neg (by rw [beq_eq_false_iff_ne.mpr (h a (List.mem_cons_self ..))]
                   exact Bool.false_ne_true),
      ih q (fun x hx => h x (List.mem_cons_of_mem _ hx))]

private theorem splitFirstAux_none {c : Char} : ∀ {l : List Char},
    (∀ a ∈ l, a ≠ c) → splitFirstAux c l = none := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons a t ih =>
    intro h
    unfold splitFirstAux
    rw [if_neg (by rw [beq_eq_false_iff_ne.mpr (h a (List.mem_cons_self ..))]
                   exact Bool.false_ne_true),
      ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]

private theorem splitLastAux_none {c : Char} : ∀ {l : List Char},
    (∀ a ∈ l, a ≠ c) → splitLastAux c l = none := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons a t ih =>
    intro h
    unfold splitLastAux
    rw [ih (fun x hx => h x (List.mem_cons_of_mem _ hx)),
      if_neg (by rw [beq_eq_false_iff_ne.mpr (h a (List.mem_cons_self ..))]
                 exact Bool.false_ne_true)]

private theorem splitLastAux_append {c : Char} : ∀ (p : List Char) {q : List Char},
    (∀ a ∈ q, a ≠ c) → splitLastAux c (p ++ c :: q) = some (p, q) := by
  intro p
  induction p with
  | nil =>
    intro q h
    rw [List.nil_append]
    unfold splitLastAux
    rw [splitLastAux_none h, if_pos (beq_self_eq_true c)]
  | cons a t ih =>
    intro q h
    rw [List.cons_append]
    unfold splitLastAux
    rw [ih h]

private theorem splitFirstChar_ofList {c : Char} {p q : List Char}
    (h : ∀ a ∈ p, a ≠ c) :
    splitFirstChar c (String.ofList (p ++ c :: q))
      = some (String.ofList p, String.ofList q) := by
  unfold splitFirstChar
  rw [String.toList_ofList, splitFirstAux_append q h]

private theorem splitFirstChar_ofList_none {c : Char} {l : List Char}
    (h : ∀ a ∈ l, a ≠ c) : splitFirstChar c (String.ofList l) = none := by
  unfold splitFirstChar
  rw [String.toList_ofList, splitFirstAux_none h]

private theorem splitLastChar_ofList {c : Char} {p q : List Char}
    (h : ∀ a ∈ q, a ≠ c) :
    splitLastChar c (String.ofList (p ++ c :: q))
      = some (String.ofList p, String.ofList q) := by
  unfold splitLastChar
  rw [String.toList_ofList, splitLastAux_append p h]

private theorem afterPrefix_ofList {pre : String} {t : List Char} :
    afterPrefix (String.ofList (pre.toList ++ t)) pre = some (String.ofList t) := by
  unfold afterPrefix
  rw [if_pos (by
      rw [String.startsWith_string_iff, String.toList_ofList]
      exact List.prefix_append _ _),
    String.toList_ofList, List.drop_left]

/-! #### Component lemmas -/

private theorem toList_ne_nil {s : String} (h : s ≠ "") : s.toList ≠ [] := by
  intro hl
  exact h (by rw [← String.ofList_toList (s := s), hl])

private theorem userInfoChars_ne {cfg : ConnectConfig} {d : Char}
    (hd : uriSafeChar d = false) (hcolon : (':' : Char) ≠ d) :
    ∀ a ∈ userInfoChars cfg, a ≠ d := by
  unfold userInfoChars
  refine ne_append (ne_of_uriSafe (uriSafeChar_percentEncode _) hd) ?_
  split
  · exact ne_cons hcolon (ne_of_uriSafe (uriSafeChar_percentEncode _) hd)
  · intro a ha; cases ha

private theorem hostPortChars_ne {cfg : ConnectConfig} {d : Char}
    (hhostsafe : ∀ c ∈ cfg.host.toList, uriSafeChar c = true)
    (hd : uriSafeChar d = false) (hcolon : (':' : Char) ≠ d) :
    ∀ a ∈ hostPortChars cfg, a ≠ d :=
  ne_append (ne_of_uriSafe hhostsafe hd)
    (ne_cons hcolon (ne_of_uriSafe (uriSafeChar_repr _) hd))

private theorem pathChars_ne {cfg : ConnectConfig} {d : Char}
    (hd : uriSafeChar d = false) (hslash : ('/' : Char) ≠ d) :
    ∀ a ∈ pathChars cfg, a ≠ d := by
  unfold pathChars
  split
  · exact ne_cons hslash (ne_of_uriSafe (uriSafeChar_percentEncode _) hd)
  · intro a ha; cases ha

private theorem uriBody_ne_question {cfg : ConnectConfig}
    (hhostsafe : ∀ c ∈ cfg.host.toList, uriSafeChar c = true) :
    ∀ a ∈ uriBody cfg, a ≠ '?' :=
  ne_append (userInfoChars_ne (by decide) (by decide))
    (ne_cons (by decide)
      (ne_append (hostPortChars_ne hhostsafe (by decide) (by decide))
        (pathChars_ne (by decide) (by decide))))

private theorem authority_ne_slash {cfg : ConnectConfig}
    (hhostsafe : ∀ c ∈ cfg.host.toList, uriSafeChar c = true) :
    ∀ a ∈ userInfoChars cfg ++ '@' :: hostPortChars cfg, a ≠ '/' :=
  ne_append (userInfoChars_ne (by decide) (by decide))
    (ne_cons (by decide) (hostPortChars_ne hhostsafe (by decide) (by decide)))

private theorem not_startsWith_bracket {a : Char} {l : List Char}
    (ha : uriSafeChar a = true) : (String.ofList (a :: l)).startsWith "[" = false := by
  rw [String.startsWith_string_eq_false_iff]
  intro hpre
  obtain ⟨t, ht⟩ := hpre
  have ht2 : ("[" : String).toList ++ t = a :: l := by rw [ht, String.toList_ofList]
  rw [show ("[" : String).toList = ['['] from by decide, List.cons_append,
    List.nil_append] at ht2
  injection ht2 with h1 _
  rw [← h1] at ha
  exact absurd ha (by decide)

private theorem applyUserInfo_render (cfg : ConnectConfig) :
    applyUserInfo {} (String.ofList (userInfoChars cfg))
      = { ({} : ConnectConfig) with user := cfg.user, password := cfg.password } := by
  unfold applyUserInfo userInfoChars
  cases hpw : cfg.password with
  | none =>
    rw [List.append_nil,
      splitFirstChar_ofList_none
        (ne_of_uriSafe (uriSafeChar_percentEncode cfg.user) (by decide)),
      String.ofList_toList, percentDecode_percentEncode]
  | some pw =>
    rw [splitFirstChar_ofList
        (q := (percentEncode pw).toList)
        (ne_of_uriSafe (uriSafeChar_percentEncode cfg.user) (by decide))]
    simp only [String.ofList_toList, percentDecode_percentEncode]

private theorem parsePort_render {n : Nat} (hpos : 0 < n) (hmax : n ≤ 65535) :
    parsePort (String.ofList (Nat.repr n).toList) = .ok (UInt16.ofNat n) := by
  rw [String.ofList_toList]
  unfold parsePort
  rw [Nat.toNat?_repr]
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  rw [if_pos ⟨hpos, hmax⟩]

private theorem applyHostPort_render {cfg base : ConnectConfig}
    (hhost : cfg.host ≠ "")
    (hhostsafe : ∀ c ∈ cfg.host.toList, uriSafeChar c = true)
    (hport : cfg.port ≠ 0) :
    applyHostPort base (String.ofList (hostPortChars cfg))
      = .ok { base with host := cfg.host, port := cfg.port } := by
  have hpos : 0 < cfg.port.toNat := by
    rcases Nat.eq_zero_or_pos cfg.port.toNat with h | h
    · exact absurd (UInt16.toNat_inj.mp (by rw [h]; rfl)) hport
    · exact h
  have hmax : cfg.port.toNat ≤ 65535 := by
    have := UInt16.toNat_lt cfg.port
    omega
  cases hl : cfg.host.toList with
  | nil => exact absurd hl (toList_ne_nil hhost)
  | cons a rest =>
    have ha : uriSafeChar a = true := hhostsafe a (by rw [hl]; exact List.mem_cons_self ..)
    have hne : (String.ofList (a :: rest)).isEmpty = false := by
      rw [← hl, String.ofList_toList]
      exact String.isEmpty_eq_false_iff.mpr hhost
    unfold applyHostPort hostPortChars
    rw [hl, List.cons_append,
      if_neg (by rw [not_startsWith_bracket ha]; exact Bool.false_ne_true),
      show (a :: (rest ++ ':' :: (Nat.repr cfg.port.toNat).toList))
        = (a :: rest) ++ ':' :: (Nat.repr cfg.port.toNat).toList from rfl,
      splitLastChar_ofList
        (ne_of_uriSafe (uriSafeChar_repr cfg.port.toNat) (by decide))]
    simp only [parsePort_render hpos hmax, hne, Bool.false_eq_true, if_false]
    rw [← hl, String.ofList_toList, UInt16.ofNat_toNat]

private theorem applyPath_render {base : ConnectConfig} {db : String} (hdb : db ≠ "") :
    applyPath base (percentEncode db) = { base with database := some db } := by
  unfold applyPath
  rw [percentDecode_percentEncode,
    if_neg (by rw [String.isEmpty_eq_false_iff.mpr hdb]; exact Bool.false_ne_true)]

/-- **Render → parse roundtrip**: `parseUri` recovers exactly the components
`renderUri` writes — user, password, host, port, and database — with the
percent-encoded fields decoded back to their original bytes.

The hypotheses are what a URI authority genuinely imposes, not proof artifacts:
the host must carry no delimiter and no `[` (everything else is percent-escaped
by `renderUri`), the port must be non-zero, and the user and database names must
be non-empty — an empty one is indistinguishable from an absent one on the
wire. -/
theorem parseUri_renderUri {cfg : ConnectConfig}
    (huser : cfg.user ≠ "")
    (hhost : cfg.host ≠ "")
    (hhostsafe : ∀ c ∈ cfg.host.toList, uriSafeChar c = true)
    (hport : cfg.port ≠ 0)
    (hdbne : ∀ db ∈ cfg.database, db ≠ "") :
    ∃ cfg', parseUri (renderUri cfg) = .ok cfg' ∧
      cfg'.user = cfg.user ∧ cfg'.password = cfg.password ∧
      cfg'.host = cfg.host ∧ cfg'.port = cfg.port ∧
      cfg'.database = cfg.database := by
  have huserEmpty : (cfg.user).isEmpty = false := String.isEmpty_eq_false_iff.mpr huser
  have hscheme : parseUri (renderUri cfg)
      = parseAfterScheme (String.ofList (uriBody cfg)) none := by
    unfold parseUri renderUri
    rw [afterPrefix_ofList (pre := "postgresql://")]
    show (match splitFirstChar '?' (String.ofList (uriBody cfg)) with
          | some (b, q) => parseAfterScheme b (some q)
          | none => parseAfterScheme (String.ofList (uriBody cfg)) none) = _
    rw [splitFirstChar_ofList_none (uriBody_ne_question hhostsafe)]
  have hauth : ∀ path? : Option String,
      parseAuthority (String.ofList (userInfoChars cfg ++ '@' :: hostPortChars cfg))
          path? none
        = parseHostPart (applyUserInfo {} (String.ofList (userInfoChars cfg)))
            (String.ofList (hostPortChars cfg)) path? none := by
    intro path?
    unfold parseAuthority
    rw [splitLastChar_ofList (hostPortChars_ne hhostsafe (by decide) (by decide))]
  cases hdbv : cfg.database with
  | none =>
    refine ⟨{ ({} : ConnectConfig) with
                user := cfg.user, password := cfg.password,
                host := cfg.host, port := cfg.port },
            ?_, rfl, rfl, rfl, rfl, rfl⟩
    · rw [hscheme]
      unfold parseAfterScheme uriBody pathChars
      rw [hdbv, List.append_nil,
        splitFirstChar_ofList_none (authority_ne_slash hhostsafe), hauth none,
        applyUserInfo_render]
      unfold parseHostPart
      rw [applyHostPort_render hhost hhostsafe hport]
      unfold finishUri
      simp only [huserEmpty, Bool.false_eq_true, if_false]
  | some db =>
    have hdb0 : db ≠ "" := hdbne db (Option.mem_def.mpr hdbv)
    refine ⟨{ ({} : ConnectConfig) with
                user := cfg.user, password := cfg.password,
                host := cfg.host, port := cfg.port, database := some db },
            ?_, rfl, rfl, rfl, rfl, rfl⟩
    · rw [hscheme]
      unfold parseAfterScheme uriBody pathChars
      rw [hdbv,
        show userInfoChars cfg ++
              '@' :: (hostPortChars cfg ++ '/' :: (percentEncode db).toList)
            = (userInfoChars cfg ++ '@' :: hostPortChars cfg) ++
              '/' :: (percentEncode db).toList from by
          rw [List.append_assoc, List.cons_append],
        splitFirstChar_ofList (authority_ne_slash hhostsafe)]
      simp only [hauth, applyUserInfo_render, parseHostPart,
        applyHostPort_render hhost hhostsafe hport, String.ofList_toList,
        applyPath_render hdb0, finishUri, huserEmpty, Bool.false_eq_true, if_false]

end ConnectConfig

end Pg
