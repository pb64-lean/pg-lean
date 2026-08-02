import Pg.Sasl.Scram

/-!
SCRAM-SHA-256 against the RFC 7677 §3 example exchange (user "user",
password "pencil", client nonce "rOprNGfwEbeRWgbNEkqO"): every message must
match the RFC byte for byte, the genuine server signature must verify, and
tampered/malformed server messages must be rejected with the right error.
-/

open Pg.Sasl

def expect (cond : Bool) (msg : String) : IO Unit := do
  unless cond do throw (IO.userError msg)

def rfcNonce : String := "rOprNGfwEbeRWgbNEkqO"

def rfcServerFirst : String :=
  "r=rOprNGfwEbeRWgbNEkqO%hvYDpWUa2RaTCAfuxFIlj)hNlF$k0,s=W22ZaJ0SNY7soEsUEjb6gQ==,i=4096"

def rfcClientFinal : String :=
  "c=biws,r=rOprNGfwEbeRWgbNEkqO%hvYDpWUa2RaTCAfuxFIlj)hNlF$k0,p=dHzbZapWIk4jUhN+Ute9ytag9zjfMHgsqmmiz7AndVQ="

def rfcServerFinal : String := "v=6rriTRBi23WpRR/wtup+mMhUZUn/dB5nLTJRsjl95G4="

def plusBinding : ByteArray :=
  ByteArray.mk #[0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07,
    0x08, 0x09, 0x0a, 0x0b, 0x0c, 0x0d, 0x0e, 0x0f,
    0x10, 0x11, 0x12, 0x13, 0x14, 0x15, 0x16, 0x17,
    0x18, 0x19, 0x1a, 0x1b, 0x1c, 0x1d, 0x1e, 0x1f]

def plusCbind : String :=
  "cD10bHMtc2VydmVyLWVuZC1wb2ludCwsAAECAwQFBgcICQoLDA0ODxAREhMUFRYXGBkaGxwdHh8="

def plusClientFinal : String :=
  "c=" ++ plusCbind ++
    ",r=rOprNGfwEbeRWgbNEkqO%hvYDpWUa2RaTCAfuxFIlj)hNlF$k0" ++
    ",p=nY1Wus9a+gM2DrbQ1msXFgyhW6KM5ktOxWiU+/P/EGY="

def plusServerFinal : String := "v=RwppMGddhz/J0lFYaRReBjXcQeNUFP5Qc76Lo5Exrig="

def expectFinalError (c : Scram.Client) (serverFirst : String) (want : Scram.Error)
    (label : String) : IO Unit := do
  match Scram.clientFinal c serverFirst with
  | .ok _ => throw (IO.userError s!"{label}: expected {repr want}, got ok")
  | .error e =>
    unless e == want do throw (IO.userError s!"{label}: expected {repr want}, got {repr e}")

def main : IO Unit := do
  -- the full RFC 7677 exchange, byte for byte
  let (c, first) := Scram.clientFirst "user" "pencil" rfcNonce
  expect (first == "n,,n=user,r=rOprNGfwEbeRWgbNEkqO") s!"client-first: {first}"
  let (c, final) ← match Scram.clientFinal c rfcServerFirst with
    | .ok r => pure r
    | .error e => throw (IO.userError s!"clientFinal: {repr e}")
  expect (final == rfcClientFinal) s!"client-final: {final}"
  match Scram.verifyServerFinal c rfcServerFinal with
  | .ok () => pure ()
  | .error e => throw (IO.userError s!"verifyServerFinal: {repr e}")

  -- All three GS2 channel-binding flags have distinct, exact wire headers.
  expect (Scram.ChannelBinding.none.gs2Header == "n,,") "GS2 n header"
  expect (Scram.ChannelBinding.supportedNotUsed.gs2Header == "y,,") "GS2 y header"
  expect ((Scram.ChannelBinding.tlsServerEndPoint plusBinding).gs2Header ==
    "p=tls-server-end-point,,") "GS2 p header"
  expect (Scram.ChannelBinding.none.encoded == "biws") "GS2 n cbind"
  expect (Scram.ChannelBinding.supportedNotUsed.encoded == "eSws") "GS2 y cbind"
  expect ((Scram.ChannelBinding.tlsServerEndPoint plusBinding).encoded == plusCbind)
    "GS2 p cbind"
  expect (Scram.ChannelBinding.none.mechanism == Scram.mechanismName)
    "n uses non-PLUS mechanism"
  expect (Scram.ChannelBinding.supportedNotUsed.mechanism == Scram.mechanismName)
    "y uses non-PLUS mechanism"
  expect ((Scram.ChannelBinding.tlsServerEndPoint plusBinding).mechanism ==
    Scram.plusMechanismName) "p uses PLUS mechanism"

  -- The explicit `y` construction is a normal SCRAM-SHA-256 exchange whose
  -- first message and cbind input both retain the downgrade-detection flag.
  let (cy, yFirst) := Scram.clientFirstWithChannelBinding
    .supportedNotUsed "user" "pencil" rfcNonce
  expect (yFirst == "y,,n=user,r=rOprNGfwEbeRWgbNEkqO") "GS2 y client-first"
  let (_, yFinal) ← match Scram.clientFinal cy rfcServerFirst with
    | .ok r => pure r
    | .error e => throw (IO.userError s!"GS2 y clientFinal: {repr e}")
  expect (yFinal.startsWith
    "c=eSws,r=rOprNGfwEbeRWgbNEkqO%hvYDpWUa2RaTCAfuxFIlj)hNlF$k0,")
    "GS2 y client-final"

  -- SCRAM-SHA-256-PLUS uses the same RFC 7677 password/nonce/salt. These
  -- independently calculated KATs pin the SaltedPassword, proof, and server
  -- signature; only the GS2 header and cbind data alter AuthMessage.
  let some salt := Pg.Crypto.Base64.decode? "W22ZaJ0SNY7soEsUEjb6gQ=="
    | throw (IO.userError "PLUS KAT salt")
  let salted := Pg.Crypto.pbkdf2HmacSha256 "pencil".toUTF8 salt 4096 32
  expect (Pg.Crypto.Base64.encode salted ==
    "xKSVEDI6tPlSysH6mUQZOeeOp01r6B3fcJbodRPcYV0=") "PLUS KAT SaltedPassword"
  let (cp, plusFirst) := Scram.clientFirstWithChannelBinding
    (.tlsServerEndPoint plusBinding) "user" "pencil" rfcNonce
  expect (plusFirst == "p=tls-server-end-point,,n=user,r=rOprNGfwEbeRWgbNEkqO")
    s!"PLUS client-first: {plusFirst}"
  let (cp, plusFinal) ← match Scram.clientFinal cp rfcServerFirst with
    | .ok r => pure r
    | .error e => throw (IO.userError s!"PLUS clientFinal: {repr e}")
  expect (plusFinal == plusClientFinal) s!"PLUS client-final: {plusFinal}"
  match Scram.verifyServerFinal cp plusServerFinal with
  | .ok () => pure ()
  | .error e => throw (IO.userError s!"PLUS verifyServerFinal: {repr e}")

  -- A one-byte binding change changes c= and therefore both sides of the
  -- AuthMessage. The correct server signature must not verify for it.
  let wrongBinding := ByteArray.mk #[0x01, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07,
    0x08, 0x09, 0x0a, 0x0b, 0x0c, 0x0d, 0x0e, 0x0f,
    0x10, 0x11, 0x12, 0x13, 0x14, 0x15, 0x16, 0x17,
    0x18, 0x19, 0x1a, 0x1b, 0x1c, 0x1d, 0x1e, 0x1f]
  let wrongCbind :=
    "cD10bHMtc2VydmVyLWVuZC1wb2ludCwsAQECAwQFBgcICQoLDA0ODxAREhMUFRYXGBkaGxwdHh8="
  let wrongProof := "BFPVDm2vYB3fEXUKVuNENqNttoPssq9SZSnYz2iZIlY="
  let (cWrong, _) := Scram.clientFirstWithChannelBinding
    (.tlsServerEndPoint wrongBinding) "user" "pencil" rfcNonce
  let (cWrong, wrongFinal) ← match Scram.clientFinal cWrong rfcServerFirst with
    | .ok r => pure r
    | .error e => throw (IO.userError s!"wrong-bind clientFinal: {repr e}")
  expect (wrongFinal.startsWith ("c=" ++ wrongCbind ++ ",")) "wrong binding changes c="
  expect (wrongFinal.endsWith (",p=" ++ wrongProof)) "wrong binding changes proof"
  expect (!plusClientFinal.endsWith (",p=" ++ wrongProof)) "wrong proof differs from KAT"
  expect ((Scram.verifyServerFinal cWrong plusServerFinal)
    matches .error .badServerSignature) "wrong binding changes server signature"

  -- a forged server signature must not verify
  expect ((Scram.verifyServerFinal c "v=AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA=")
    matches .error .badServerSignature) "forged signature rejected"
  -- server-reported failure surfaces its message
  expect ((Scram.verifyServerFinal c "e=other-error")
    matches .error (.serverRejected "other-error")) "e= surfaces"
  expect ((Scram.verifyServerFinal c "x=?")
    matches .error (.malformedServerMessage _)) "junk server-final rejected"

  -- a different password produces a different proof (and would fail server-side)
  let (cw, _) := Scram.clientFirst "user" "wrong" rfcNonce
  match Scram.clientFinal cw rfcServerFirst with
  | .ok (_, finalW) => expect (finalW != rfcClientFinal) "wrong password differs"
  | .error e => throw (IO.userError s!"clientFinal wrong pw: {repr e}")

  -- malformed / hostile server-first variants
  let fresh := (Scram.clientFirst "user" "pencil" rfcNonce).1
  expectFinalError fresh "r=WRONGnonce,s=W22ZaJ0SNY7soEsUEjb6gQ==,i=4096"
    .nonceMismatch "nonce not extending ours"
  expectFinalError fresh ("m=ext," ++ rfcServerFirst)
    .unsupportedExtension "mandatory extension"
  expectFinalError fresh "r=rOprNGfwEbeRWgbNEkqOx,s=!!!,i=4096"
    (.malformedServerMessage "salt is not valid base64") "bad salt"
  expectFinalError fresh "r=rOprNGfwEbeRWgbNEkqOx,s=W22ZaJ0SNY7soEsUEjb6gQ==,i=many"
    (.malformedServerMessage "iteration count is not a number") "bad iteration count"
  expectFinalError fresh "r=rOprNGfwEbeRWgbNEkqOx,s=W22ZaJ0SNY7soEsUEjb6gQ==,i=0"
    (.iterationCountOutOfRange 0) "zero iterations"
  expectFinalError fresh "r=rOprNGfwEbeRWgbNEkqOx,s=W22ZaJ0SNY7soEsUEjb6gQ==,i=999999999"
    (.iterationCountOutOfRange 999999999) "iteration bomb"
  expectFinalError fresh "r=rOprNGfwEbeRWgbNEkqOx"
    (.malformedServerMessage "expected r=,s=,i= attributes") "truncated server-first"

  -- saslname escaping
  expect (Scram.saslName "a=b,c" == "a=3Db=2Cc") "saslname escaping"

  -- nonce generator shape (printable base64, 24 chars, comma-free)
  let n1 ← Scram.genNonce
  let n2 ← Scram.genNonce
  expect (n1.length == 24 && !n1.toList.contains ',') "nonce shape"
  expect (n1 != n2) "nonces differ"

  IO.println "all scram assertions passed"
