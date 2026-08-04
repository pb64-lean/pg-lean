module

public import Pg.Crypto.Sha256
public import Pg.Crypto.Hmac
public import Pg.Crypto.Pbkdf2
public import Pg.Crypto.Base64

public section

namespace Pg
namespace Sasl
namespace Scram

/-!
Client-side SCRAM-SHA-256 and SCRAM-SHA-256-PLUS (RFC 5802/7677). Pure
sub-state-machine: the connection machine chooses the GS2 channel-binding
flag, feeds it server messages, and sends whatever strings it returns.

Password normalization: SASLprep (RFC 4013) is the identity on printable
ASCII, which we pass through exactly; non-ASCII passwords are sent as
unnormalized UTF-8 (documented compromise, matching several production
drivers).
-/

def mechanismName : String := "SCRAM-SHA-256"

def plusMechanismName : String := "SCRAM-SHA-256-PLUS"

/-- The GS2 channel-binding choice made before sending the client-first
message.

* `none` emits `n`: the client has no usable channel binding.
* `supportedNotUsed` emits `y`: the client supports channel binding but
  believes the server does not. A capable server can use this to detect a
  stripped `-PLUS` mechanism advertisement.
* `tlsServerEndPoint data` emits `p=tls-server-end-point` and binds the SCRAM
  proof to `data`, the RFC 5929 certificate hash.
-/
inductive ChannelBinding where
  | none
  | supportedNotUsed
  | tlsServerEndPoint (data : ByteArray)
  deriving Inhabited

namespace ChannelBinding

def gs2Header : ChannelBinding → String
  | .none => "n,,"
  | .supportedNotUsed => "y,,"
  | .tlsServerEndPoint _ => "p=tls-server-end-point,,"

/-- The SASL mechanism name required by this GS2 choice. -/
def mechanism : ChannelBinding → String
  | .tlsServerEndPoint _ => plusMechanismName
  | _ => mechanismName

/-- Bytes encoded in the client-final `c=` attribute: the exact GS2 header,
followed by the channel-binding data for `p` (RFC 5802 §5). -/
def input (binding : ChannelBinding) : ByteArray :=
  binding.gs2Header.toUTF8 ++
    match binding with
    | .tlsServerEndPoint data => data
    | _ => ByteArray.empty

def encoded (binding : ChannelBinding) : String :=
  Crypto.Base64.encode binding.input

end ChannelBinding

/-- Upper bound on the server-supplied PBKDF2 iteration count (2^24), so a
hostile server cannot make the client burn unbounded CPU. PostgreSQL's
default is 4096. -/
def maxIterations : Nat := 16777216

inductive Error where
  | malformedServerMessage (why : String)
  | nonceMismatch
  | iterationCountOutOfRange (i : Nat)
  | unsupportedExtension
  | serverRejected (message : String)
  | badServerSignature
  deriving Repr, Inhabited, BEq

inductive Phase where
  | sentFirst
  | sentFinal (serverSignature : ByteArray)
  deriving Inhabited

structure Client where
  password : String
  nonce : String
  clientFirstBare : String
  channelBinding : ChannelBinding
  phase : Phase
  deriving Inhabited

/-- RFC 5802 saslname escaping for the `n=` attribute. -/
def saslName (s : String) : String :=
  (s.replace "=" "=3D").replace "," "=2C"

/-- Not constant-time (documented; Lean offers no timing guarantees anywhere). -/
private def bytesEq (a b : ByteArray) : Bool := a.data == b.data

/-- Byte-wise XOR (the SCRAM proof combiner). Public so `clientFinal_spec`
can state the exact proof construction. -/
def xorBytes (a b : ByteArray) : ByteArray := Id.run do
  let mut out := ByteArray.empty
  for i in [0:a.size] do
    out := out.push (a.get! i ^^^ b.get! i)
  return out

/-- The value of an attribute like `r=...`: everything past the 2-byte ASCII
prefix. Public so the SCRAM laws can speak about parsed attribute values. -/
def valueAfterPrefix (part : String) : String :=
  (String.fromUTF8? (part.toUTF8.extract 2 part.toUTF8.size)).getD ""

/-- Split a message into attributes at a separator character.

Deliberately *not* `String.splitOn`: `String.splitOnAux` is `@[irreducible]`
and core 4.31 ships no lemmas about it whatsoever, so a `String.splitOn`-based
parser is opaque to the kernel. `List.splitOn` has a full lemma set, and the
two agree for a single-character separator — that is what makes
`parseServerFirst_render` provable. -/
def splitOnChar (c : Char) (s : String) : List String :=
  (s.toList.splitOn c).map String.ofList

/-- Returns the sub-machine and client-first message for an explicit GS2
channel-binding choice. PostgreSQL ignores the `n=` field (it uses the
startup-message user), but sending it costs nothing and makes the exchange
match the RFC examples byte for byte. The nonce must be fresh per connection
(`genNonce`). -/
def clientFirstWithChannelBinding (binding : ChannelBinding)
    (user password nonce : String) : Client × String :=
  let bare := "n=" ++ saslName user ++ ",r=" ++ nonce
  ({ password, nonce, clientFirstBare := bare, channelBinding := binding,
      phase := .sentFirst },
    binding.gs2Header ++ bare)

/-- Backwards-compatible non-channel-binding client-first message
(`n,,n=<user>,r=<nonce>`). -/
def clientFirst (user password nonce : String) : Client × String :=
  clientFirstWithChannelBinding .none user password nonce

structure ServerFirst where
  nonce : String
  salt : ByteArray
  iterations : Nat
  deriving Inhabited

def parseServerFirst (ourNonce : String) (msg : String) : Except Error ServerFirst :=
  match splitOnChar ',' msg with
  | r :: s :: i :: _ =>
    if r.startsWith "m=" then throw .unsupportedExtension
    else if !r.startsWith "r=" then throw (.malformedServerMessage "expected r=")
    else if !s.startsWith "s=" then throw (.malformedServerMessage "expected s=")
    else if !i.startsWith "i=" then throw (.malformedServerMessage "expected i=")
    else if !(valueAfterPrefix r).startsWith ourNonce then throw .nonceMismatch
    else
      match Crypto.Base64.decode? (valueAfterPrefix s) with
      | none => throw (.malformedServerMessage "salt is not valid base64")
      | some salt =>
        match (valueAfterPrefix i).toNat? with
        | none => throw (.malformedServerMessage "iteration count is not a number")
        | some iterations =>
          if iterations == 0 || iterations > maxIterations then
            throw (.iterationCountOutOfRange iterations)
          else
            .ok { nonce := valueAfterPrefix r, salt, iterations }
  | _ => throw (.malformedServerMessage "expected r=,s=,i= attributes")

/-- Consumes the server-first message; returns the advanced sub-machine
(holding the expected server signature) and the client-final message. The
`c=` value is base64 of the exact GS2 header plus any channel-binding data. -/
def clientFinal (c : Client) (serverFirst : String) : Except Error (Client × String) :=
  match c.phase with
  | .sentFinal _ => throw (.malformedServerMessage "client-final already sent")
  | .sentFirst =>
    match parseServerFirst c.nonce serverFirst with
    | .error e => .error e
    | .ok sf =>
      let saltedPassword := Crypto.pbkdf2HmacSha256 c.password.toUTF8 sf.salt sf.iterations 32
      let clientKey := Crypto.hmacSha256 saltedPassword "Client Key".toUTF8
      let storedKey := Crypto.sha256 clientKey
      let withoutProof := "c=" ++ c.channelBinding.encoded ++ ",r=" ++ sf.nonce
      let authMessage := c.clientFirstBare ++ "," ++ serverFirst ++ "," ++ withoutProof
      let clientSignature := Crypto.hmacSha256 storedKey authMessage.toUTF8
      let proof := xorBytes clientKey clientSignature
      let serverKey := Crypto.hmacSha256 saltedPassword "Server Key".toUTF8
      let serverSignature := Crypto.hmacSha256 serverKey authMessage.toUTF8
      .ok ({ c with phase := .sentFinal serverSignature },
        withoutProof ++ ",p=" ++ Crypto.Base64.encode proof)

/-- Checks the server-final message (`v=<signature>` on success, `e=<msg>` on
server-reported failure) against the signature computed in `clientFinal`.
Success here means the server actually knows the password's verifier — it is
mutual authentication, not a formality. The comparison is not constant-time
(documented; Lean offers no timing guarantees anywhere). -/
def verifyServerFinal (c : Client) (serverFinal : String) : Except Error Unit :=
  match c.phase with
  | .sentFirst => throw (.malformedServerMessage "server-final before client-final")
  | .sentFinal expected =>
    match splitOnChar ',' serverFinal with
    | [] => throw (.malformedServerMessage "expected v= or e=")
    | first :: _ =>
      if first.startsWith "e=" then throw (.serverRejected (valueAfterPrefix first))
      else if !first.startsWith "v=" then throw (.malformedServerMessage "expected v= or e=")
      else
        match Crypto.Base64.decode? (valueAfterPrefix first) with
        | none => throw (.malformedServerMessage "signature is not valid base64")
        | some sig =>
          if bytesEq sig expected then .ok () else throw .badServerSignature

/-- Fresh per-connection nonce: 18 CSPRNG bytes, base64 (24 chars, printable,
comma-free) — the same shape libpq uses. -/
def genNonce : IO String := do
  let bytes ← IO.getRandomBytes 18
  pure (Crypto.Base64.encode bytes)

/-!
### SCRAM laws

Kernel-checked construction laws for the exchange. The crypto primitives
(HMAC-SHA-256, PBKDF2, SHA-256) are treated as opaque byte functions — no
cryptographic assumption is used, so every law below holds for *any*
implementation of those interfaces, in particular the concrete lawful one:

- `valueAfterPrefix_append`: attribute render/parse roundtrip — reading a
  rendered 2-byte-prefixed attribute (`r=`, `s=`, `i=`, `c=`, `p=`, `v=`)
  recovers the rendered value.
- `clientFirst_message`/`clientFirst_state`: the client-first message is
  exactly `gs2Header ++ "n=" ++ saslName user ++ ",r=" ++ nonce`, with the
  bare part and nonce retained verbatim in the sub-machine.
- `parseServerFirst_spec`/`parseServerFirst_nonce_extends`: a parsed
  server-first has `r=`,`s=`,`i=` attributes in order, in-range iterations,
  and a server nonce that **extends the client nonce** — nonce substitution
  is rejected.
- `parseServerFirst_render`: the converse direction — a rendered server-first
  message (`renderServerFirst`) parses back to exactly the nonce, salt and
  iteration count that were rendered, given RFC 5802's own comma-free
  restriction on attribute values.
- `clientFinal_spec`: the exact RFC 5802 client-final message and expected
  server signature: `c=<b64(gs2+cbind)>,r=<server nonce>,p=<b64 proof>`
  with the signature over exactly
  `client-first-bare "," server-first "," client-final-without-proof`.
- `verifyServerFinal_spec`: verification succeeds only for a `v=` attribute
  carrying exactly the expected signature — mutual authentication checks
  the byte-exact HMAC and nothing else.
-/

private theorem fromUTF8?_toUTF8 (s : String) : String.fromUTF8? s.toUTF8 = some s := by
  simp only [String.fromUTF8?, String.toUTF8_eq_toByteArray]
  rw [dif_pos s.isValidUTF8]
  rfl

/-- Attribute render/parse roundtrip for any 2-byte prefix. -/
theorem valueAfterPrefix_append (p v : String) (hp : p.utf8ByteSize = 2) :
    valueAfterPrefix (p ++ v) = v := by
  unfold valueAfterPrefix
  rw [String.toUTF8_eq_toByteArray, String.toByteArray_append,
    ByteArray.extract_append_eq_right
      (by rw [String.size_toByteArray, hp])
      (by rw [ByteArray.size_append]),
    ← String.toUTF8_eq_toByteArray, fromUTF8?_toUTF8]
  rfl

/-- The client-first message is exactly the GS2 header followed by the bare
part `n=<user>,r=<nonce>`. -/
theorem clientFirst_message (binding : ChannelBinding) (user password nonce : String) :
    (clientFirstWithChannelBinding binding user password nonce).2 =
      binding.gs2Header ++ ("n=" ++ saslName user ++ ",r=" ++ nonce) := by rfl

/-- The sub-machine retains the password, nonce, bare client-first, and
channel binding verbatim, and starts in `sentFirst`. -/
theorem clientFirst_state (binding : ChannelBinding) (user password nonce : String) :
    (clientFirstWithChannelBinding binding user password nonce).1 =
      { password, nonce, clientFirstBare := "n=" ++ saslName user ++ ",r=" ++ nonce,
        channelBinding := binding, phase := .sentFirst } := by rfl

/-- Everything `parseServerFirst` accepts: `r=`,`s=`,`i=` attributes in wire
order, iterations in `(0, maxIterations]`, salt from valid base64 — and a
server nonce extending ours. -/
theorem parseServerFirst_spec {ourNonce msg : String} {sf : ServerFirst}
    (h : parseServerFirst ourNonce msg = .ok sf) :
    sf.nonce.startsWith ourNonce = true ∧
    0 < sf.iterations ∧ sf.iterations ≤ maxIterations ∧
    ∃ r s i rest, splitOnChar ',' msg = r :: s :: i :: rest ∧
      r.startsWith "r=" = true ∧ s.startsWith "s=" = true ∧ i.startsWith "i=" = true ∧
      sf.nonce = valueAfterPrefix r ∧
      Crypto.Base64.decode? (valueAfterPrefix s) = some sf.salt ∧
      (valueAfterPrefix i).toNat? = some sf.iterations := by
  revert h
  fun_cases parseServerFirst ourNonce msg <;> intro h <;> cases h
  rename_i r s i rest hsplit hm hr hs hi hnonce salt hsalt iterations hiter hrange
  simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq, not_or] at hrange
  refine ⟨?_, by show 0 < iterations; omega, by show iterations ≤ maxIterations; omega,
    r, s, i, rest, hsplit, ?_, ?_, ?_, rfl, hsalt, hiter⟩ <;> simp_all

/-- **The server nonce must extend the client nonce** — `parseServerFirst`
accepts nothing else. -/
theorem parseServerFirst_nonce_extends {ourNonce msg : String} {sf : ServerFirst}
    (h : parseServerFirst ourNonce msg = .ok sf) :
    sf.nonce.startsWith ourNonce = true :=
  (parseServerFirst_spec h).1

/-- **Exact authentication-message construction** (RFC 5802 §3): on success
the client-final message is `c=<b64(gs2+cbind)>,r=<server nonce>,p=<b64
proof>`, the proof is `clientKey XOR HMAC(storedKey, authMessage)`, and the
retained server signature is `HMAC(serverKey, authMessage)`, where
`authMessage = client-first-bare "," server-first ","
client-final-without-proof` byte-for-byte. -/
theorem clientFinal_spec {c : Client} {serverFirst : String} {c' : Client}
    {final : String} (hphase : c.phase = .sentFirst)
    (h : clientFinal c serverFirst = .ok (c', final)) :
    ∃ sf, parseServerFirst c.nonce serverFirst = .ok sf ∧
      final = "c=" ++ c.channelBinding.encoded ++ ",r=" ++ sf.nonce ++ ",p=" ++
        Crypto.Base64.encode (xorBytes
          (Crypto.hmacSha256
            (Crypto.pbkdf2HmacSha256 c.password.toUTF8 sf.salt sf.iterations 32)
            "Client Key".toUTF8)
          (Crypto.hmacSha256
            (Crypto.sha256 (Crypto.hmacSha256
              (Crypto.pbkdf2HmacSha256 c.password.toUTF8 sf.salt sf.iterations 32)
              "Client Key".toUTF8))
            (c.clientFirstBare ++ "," ++ serverFirst ++ "," ++
              ("c=" ++ c.channelBinding.encoded ++ ",r=" ++ sf.nonce)).toUTF8)) ∧
      c'.phase = .sentFinal (Crypto.hmacSha256
        (Crypto.hmacSha256
          (Crypto.pbkdf2HmacSha256 c.password.toUTF8 sf.salt sf.iterations 32)
          "Server Key".toUTF8)
        (c.clientFirstBare ++ "," ++ serverFirst ++ "," ++
          ("c=" ++ c.channelBinding.encoded ++ ",r=" ++ sf.nonce)).toUTF8) ∧
      c'.password = c.password ∧ c'.nonce = c.nonce ∧
      c'.clientFirstBare = c.clientFirstBare := by
  unfold clientFinal at h
  rw [hphase] at h
  cases hp : parseServerFirst c.nonce serverFirst with
  | error e =>
    simp only [hp] at h
    cases h
  | ok sf =>
    simp only [hp] at h
    cases h
    exact ⟨sf, rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem bytesEq_iff {a b : ByteArray} : bytesEq a b = true ↔ a = b := by
  unfold bytesEq
  rw [beq_iff_eq]
  constructor
  · intro hd
    rcases a with ⟨da⟩
    rcases b with ⟨db⟩
    cases hd
    rfl
  · intro he
    rw [he]

/-- The RFC 5802 server-first message on the wire, from its three attribute
values. -/
def renderServerFirst (nonce salt64 iterations : String) : String :=
  "r=" ++ nonce ++ ",s=" ++ salt64 ++ ",i=" ++ iterations

private theorem splitOnChar_singleton {c : Char} {s : String} (h : c ∉ s.toList) :
    splitOnChar c s = [s] := by
  unfold splitOnChar
  rw [List.splitOn_eq_singleton h]
  simp only [List.map_cons, List.map_nil, String.ofList_toList]

private theorem splitOnChar_cons {c : Char} {p rest : List Char} (h : c ∉ p) :
    splitOnChar c (String.ofList (p ++ c :: rest)) =
      String.ofList p :: splitOnChar c (String.ofList rest) := by
  unfold splitOnChar
  rw [String.toList_ofList, List.splitOn_append_cons_self_of_not_mem h,
    String.toList_ofList, List.map_cons]

private theorem startsWith_self (p v : String) : (p ++ v).startsWith p = true := by
  rw [String.startsWith_string_iff, String.toList_append]
  exact List.prefix_append _ _

private theorem startsWith_m_of_r (v : String) : ("r=" ++ v).startsWith "m=" = false := by
  rw [String.startsWith_string_eq_false_iff, String.toList_append,
    show ("m=" : String).toList = ['m', '='] from by decide,
    show ("r=" : String).toList = ['r', '='] from by decide]
  intro hpre
  obtain ⟨t, ht⟩ := hpre
  simp only [List.cons_append] at ht
  injection ht with h1 _
  exact absurd h1 (by decide)

/-- The comma split of a rendered server-first message is exactly its three
attributes, provided the values are comma-free (RFC 5802's `value-safe-char`
grammar). -/
private theorem splitOnChar_render {nonce salt64 iters : String}
    (hn : ',' ∉ nonce.toList) (hs : ',' ∉ salt64.toList) (hi : ',' ∉ iters.toList) :
    splitOnChar ',' (renderServerFirst nonce salt64 iters) =
      ["r=" ++ nonce, "s=" ++ salt64, "i=" ++ iters] := by
  have hren : renderServerFirst nonce salt64 iters =
      String.ofList (("r=" ++ nonce).toList ++ ',' ::
        (("s=" ++ salt64).toList ++ ',' :: ("i=" ++ iters).toList)) := by
    rw [show ((("r=" ++ nonce).toList ++ ',' ::
        (("s=" ++ salt64).toList ++ ',' :: ("i=" ++ iters).toList)) : List Char) =
      (renderServerFirst nonce salt64 iters).toList from by
      unfold renderServerFirst
      simp only [String.toList_append,
        show ("r=" : String).toList = ['r', '='] from by decide,
        show (",s=" : String).toList = [',', 's', '='] from by decide,
        show (",i=" : String).toList = [',', 'i', '='] from by decide]
      simp [List.append_assoc]]
    exact String.ofList_toList.symm
  have hmemr : ',' ∉ ("r=" ++ nonce).toList := by
    rw [String.toList_append, show ("r=" : String).toList = ['r', '='] from by decide]
    simpa using hn
  have hmems : ',' ∉ ("s=" ++ salt64).toList := by
    rw [String.toList_append, show ("s=" : String).toList = ['s', '='] from by decide]
    simpa using hs
  have hmemi : ',' ∉ ("i=" ++ iters).toList := by
    rw [String.toList_append, show ("i=" : String).toList = ['i', '='] from by decide]
    simpa using hi
  rw [hren, splitOnChar_cons hmemr, splitOnChar_cons hmems]
  simp only [String.ofList_toList]
  rw [splitOnChar_singleton hmemi]

/-- **Render→parse roundtrip**: a well-formed server-first message parses back
to exactly the values that were rendered. The comma-freeness hypotheses are
RFC 5802's own `value-safe-char` restriction on attribute values (real nonces
and salts are base64, the iteration count decimal), not a proof artifact. -/
theorem parseServerFirst_render {ourNonce nonce salt64 iters : String}
    {salt : ByteArray} {iterations : Nat}
    (hn : ',' ∉ nonce.toList) (hs : ',' ∉ salt64.toList) (hi : ',' ∉ iters.toList)
    (hnonce : nonce.startsWith ourNonce = true)
    (hsalt : Crypto.Base64.decode? salt64 = some salt)
    (hiter : iters.toNat? = some iterations)
    (hpos : 0 < iterations) (hmax : iterations ≤ maxIterations) :
    parseServerFirst ourNonce (renderServerFirst nonce salt64 iters) =
      .ok { nonce, salt, iterations } := by
  have hvr : valueAfterPrefix ("r=" ++ nonce) = nonce := valueAfterPrefix_append _ _ rfl
  have hvs : valueAfterPrefix ("s=" ++ salt64) = salt64 := valueAfterPrefix_append _ _ rfl
  have hvi : valueAfterPrefix ("i=" ++ iters) = iters := valueAfterPrefix_append _ _ rfl
  have h0 : (iterations == 0) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]
    omega
  have hgt : decide (iterations > maxIterations) = false := by
    simp only [decide_eq_false_iff_not, Nat.not_lt]
    omega
  unfold parseServerFirst
  rw [splitOnChar_render hn hs hi]
  simp only [startsWith_m_of_r, startsWith_self, hvr, hvs, hvi, hnonce, hsalt, hiter,
    h0, hgt, Bool.not_true, Bool.false_eq_true, if_false, Bool.or_self]

/-- Mutual authentication is byte-exact: verification succeeds only for a
`v=` first attribute whose base64 payload is exactly the server signature
computed in `clientFinal`. -/
theorem verifyServerFinal_spec {c : Client} {serverFinal : String}
    (h : verifyServerFinal c serverFinal = .ok ()) :
    ∃ expected first rest,
      c.phase = .sentFinal expected ∧
      splitOnChar ',' serverFinal = first :: rest ∧
      first.startsWith "v=" = true ∧
      Crypto.Base64.decode? (valueAfterPrefix first) = some expected := by
  revert h
  fun_cases verifyServerFinal c serverFinal <;> intro h <;> cases h
  rename_i expected hphase first rest hsplit he hv sig hsig hbeq
  refine ⟨expected, first, rest, hphase, hsplit, ?_, ?_⟩
  · simp only [Bool.not_eq_eq_eq_not, Bool.not_true, Bool.not_eq_false] at hv
    exact hv
  · rw [hsig, bytesEq_iff.mp hbeq]

end Scram
end Sasl
end Pg
