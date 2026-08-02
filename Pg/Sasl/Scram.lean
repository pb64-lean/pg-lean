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

private def bytesEq (a b : ByteArray) : Bool := Id.run do
  if a.size != b.size then return false
  for i in [0:a.size] do
    if a.get! i != b.get! i then return false
  return true

private def xorBytes (a b : ByteArray) : ByteArray := Id.run do
  let mut out := ByteArray.empty
  for i in [0:a.size] do
    out := out.push (a.get! i ^^^ b.get! i)
  return out

/-- The value of an attribute like `r=...`: everything past the 2-byte ASCII
prefix. -/
private def valueAfterPrefix (part : String) : String :=
  let raw := part.toUTF8
  (String.fromUTF8? (raw.extract 2 raw.size)).getD ""

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

def parseServerFirst (ourNonce : String) (msg : String) : Except Error ServerFirst := do
  match msg.splitOn "," with
  | r :: s :: i :: _ =>
    if r.startsWith "m=" then throw .unsupportedExtension
    unless r.startsWith "r=" do throw (.malformedServerMessage "expected r=")
    unless s.startsWith "s=" do throw (.malformedServerMessage "expected s=")
    unless i.startsWith "i=" do throw (.malformedServerMessage "expected i=")
    let nonce := valueAfterPrefix r
    unless nonce.startsWith ourNonce do throw .nonceMismatch
    let some salt := Crypto.Base64.decode? (valueAfterPrefix s)
      | throw (.malformedServerMessage "salt is not valid base64")
    let some iterations := (valueAfterPrefix i).toNat?
      | throw (.malformedServerMessage "iteration count is not a number")
    if iterations == 0 || iterations > maxIterations then
      throw (.iterationCountOutOfRange iterations)
    pure { nonce, salt, iterations }
  | _ => throw (.malformedServerMessage "expected r=,s=,i= attributes")

/-- Consumes the server-first message; returns the advanced sub-machine
(holding the expected server signature) and the client-final message. The
`c=` value is base64 of the exact GS2 header plus any channel-binding data. -/
def clientFinal (c : Client) (serverFirst : String) : Except Error (Client × String) := do
  unless c.phase matches .sentFirst do
    throw (.malformedServerMessage "client-final already sent")
  let sf ← parseServerFirst c.nonce serverFirst
  let saltedPassword := Crypto.pbkdf2HmacSha256 c.password.toUTF8 sf.salt sf.iterations 32
  let clientKey := Crypto.hmacSha256 saltedPassword "Client Key".toUTF8
  let storedKey := Crypto.sha256 clientKey
  let withoutProof := "c=" ++ c.channelBinding.encoded ++ ",r=" ++ sf.nonce
  let authMessage := c.clientFirstBare ++ "," ++ serverFirst ++ "," ++ withoutProof
  let clientSignature := Crypto.hmacSha256 storedKey authMessage.toUTF8
  let proof := xorBytes clientKey clientSignature
  let serverKey := Crypto.hmacSha256 saltedPassword "Server Key".toUTF8
  let serverSignature := Crypto.hmacSha256 serverKey authMessage.toUTF8
  pure ({ c with phase := .sentFinal serverSignature },
    withoutProof ++ ",p=" ++ Crypto.Base64.encode proof)

/-- Checks the server-final message (`v=<signature>` on success, `e=<msg>` on
server-reported failure) against the signature computed in `clientFinal`.
Success here means the server actually knows the password's verifier — it is
mutual authentication, not a formality. The comparison is not constant-time
(documented; Lean offers no timing guarantees anywhere). -/
def verifyServerFinal (c : Client) (serverFinal : String) : Except Error Unit := do
  let .sentFinal expected := c.phase
    | throw (.malformedServerMessage "server-final before client-final")
  let first := (serverFinal.splitOn ",").headD ""
  if first.startsWith "e=" then throw (.serverRejected (valueAfterPrefix first))
  unless first.startsWith "v=" do throw (.malformedServerMessage "expected v= or e=")
  let some sig := Crypto.Base64.decode? (valueAfterPrefix first)
    | throw (.malformedServerMessage "signature is not valid base64")
  unless bytesEq sig expected do throw .badServerSignature

/-- Fresh per-connection nonce: 18 CSPRNG bytes, base64 (24 chars, printable,
comma-free) — the same shape libpq uses. -/
def genNonce : IO String := do
  let bytes ← IO.getRandomBytes 18
  pure (Crypto.Base64.encode bytes)

end Scram
end Sasl
end Pg
