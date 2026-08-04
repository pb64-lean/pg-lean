import Tls.Record
import Tls.Handshake
import Tls.Client
import HaclStar.Curve25519
import HaclStar.Hmac
import HaclStar.P256
import HaclStar.Sha256
import Pg.Crypto.Hex
import TLS13.KeySchedule
import TLS13.X509

/-!
Hermetic tests for pg-lean's sans-I/O TLS 1.3 implementation.

The synthetic peer below uses independent server-side transcript and traffic
state. No socket, wall clock, random source, certificate store, or PostgreSQL
installation is involved.
-/

open Tls

def expect (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

def must [ToString ε] (result : Except ε α) (label : String) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError s!"{label}: {error}")

def bytes (count : Nat) (value : UInt8) : ByteArray := Id.run do
  let mut out := ByteArray.empty
  for _ in [0:count] do
    out := out.push value
  return out

def u16 (value : UInt16) : ByteArray :=
  ByteArray.mk #[(value >>> 8).toUInt8, value.toUInt8]

def u24 (value : Nat) : ByteArray :=
  ByteArray.mk #[
    UInt8.ofNat (value >>> 16),
    UInt8.ofNat (value >>> 8),
    UInt8.ofNat value
  ]

def u32 (value : UInt32) : ByteArray :=
  ByteArray.mk #[
    (value >>> 24).toUInt8,
    (value >>> 16).toUInt8,
    (value >>> 8).toUInt8,
    value.toUInt8
  ]

def vec8 (value : ByteArray) : ByteArray :=
  (ByteArray.empty.push (UInt8.ofNat value.size)) ++ value

def vec16 (value : ByteArray) : ByteArray :=
  u16 (UInt16.ofNat value.size) ++ value

def vec24 (value : ByteArray) : ByteArray :=
  u24 value.size ++ value

def extension (extensionType : UInt16) (data : ByteArray) : ByteArray :=
  u16 extensionType ++ vec16 data

def encodedRecordHeader (contentType : Record.ContentType) (length : Nat) : ByteArray :=
  ByteArray.mk #[
    contentType.toUInt8, 0x03, 0x03,
    UInt8.ofNat (length >>> 8), UInt8.ofNat length
  ]

def feedRecordChunks (wire : ByteArray) (chunkSize : Nat) :
    IO (Record.Decoder × Array Record.RawRecord) := do
  let mut decoder : Record.Decoder := {}
  let mut records : Array Record.RawRecord := #[]
  let mut offset := 0
  let chunkSize := max chunkSize 1
  while offset < wire.size do
    let stop := min wire.size (offset + chunkSize)
    let (next, produced) ← must (decoder.feed (wire.extract offset stop))
      s!"record feed/{chunkSize}"
    decoder := next
    records := records ++ produced
    offset := stop
  pure (decoder, records)

def decodeSingleRecord (wire : ByteArray) : IO Record.RawRecord := do
  let (decoder, records) ← must (({} : Record.Decoder).feed wire) "decode record"
  expect decoder.buffered.isEmpty "complete record left buffered bytes"
  expect (records.size == 1) s!"expected one record, got {records.size}"
  pure records[0]!

def expectRecordError (result : Except Record.Error α)
    (predicate : Record.Error → Bool) (label : String) : IO Unit := do
  match result with
  | .ok _ => throw (IO.userError s!"{label}: expected error")
  | .error error =>
    unless predicate error do
      throw (IO.userError s!"{label}: unexpected error {error}")

def testRecordFraming : IO Unit := do
  let first ← must (Record.encodePlaintext .handshake "first".toUTF8) "encode first"
  let second ← must (Record.encodePlaintext .alert (ByteArray.mk #[1, 0])) "encode second"
  let wire := first ++ second
  for chunkSize in [1, 2, 3, 7, wire.size] do
    let (decoder, records) ← feedRecordChunks wire chunkSize
    expect decoder.buffered.isEmpty s!"record fragmentation/{chunkSize}: residual bytes"
    expect (records.size == 2) s!"record fragmentation/{chunkSize}: record count"
    expect (records[0]!.contentType == .handshake &&
      records[0]!.fragment == "first".toUTF8) "first plaintext record"
    expect (records[1]!.contentType == .alert &&
      records[1]!.fragment == ByteArray.mk #[1, 0]) "second plaintext record"

  let split := first.size - 1
  let (decoder, records) ← must (({} : Record.Decoder).feed (first.extract 0 split))
    "partial record"
  expect (records.isEmpty && !decoder.buffered.isEmpty) "partial record was not retained"
  let (decoder, records) ← must (decoder.feed (first.extract split first.size))
    "finish partial record"
  expect (decoder.buffered.isEmpty && records.size == 1) "partial record did not complete"

def testRecordProtection : IO Unit := do
  let secret := bytes 32 0x42
  let keys ← must (Record.deriveTrafficKeys secret) "derive traffic keys"
  expect (keys.key.size == 32 && keys.iv.size == 12 && keys.seq == 0)
    "derived traffic-key shape"

  let plaintext := "postgres over tls".toUTF8
  let (writeKeys, wire) ← must (Record.seal keys .applicationData plaintext 9) "seal"
  expect (writeKeys.seq == 1) "seal did not advance sequence"
  let raw ← decodeSingleRecord wire
  expect (raw.contentType == .applicationData) "ciphertext outer type"
  let (readKeys, opened) ← must (Record.open keys raw) "open"
  expect (readKeys.seq == 1) "open did not advance sequence"
  expect (opened.contentType == .applicationData) "inner content type"
  expect (opened.fragment == plaintext && opened.paddingLength == 9)
    "opened plaintext/padding"

  let tamperedWire := wire.set! (wire.size - 1) (wire.get! (wire.size - 1) ^^^ 1)
  let tampered ← decodeSingleRecord tamperedWire
  expectRecordError (Record.open keys tampered)
    (fun | .authenticationFailed => true | _ => false) "tamper rejection"

  let updated ← must keys.update "traffic update"
  expect (updated.seq == 0 && updated.secret != keys.secret &&
    updated.key != keys.key && updated.iv != keys.iv) "traffic update/reset"

  let exhausted : Record.TrafficKeys := {
    keys with seq := (0xffffffffffffffff : UInt64)
  }
  expectRecordError (Record.seal exhausted .applicationData ByteArray.empty)
    (fun | .sequenceExhausted => true | _ => false) "sequence exhaustion"

def testRecordLimits : IO Unit := do
  let maxPlain := bytes Record.maxPlaintextLength 0x61
  let _ ← must (Record.encodePlaintext .handshake maxPlain) "maximum plaintext"
  expectRecordError
    (Record.encodePlaintext .handshake (maxPlain.push 0x61))
    (fun | .plaintextTooLong _ => true | _ => false) "plaintext cap"

  let keys ← must (Record.deriveTrafficKeys (bytes 32 0x19)) "limit keys"
  let _ ← must (Record.seal keys .applicationData maxPlain) "maximum protected fragment"
  expectRecordError
    (Record.seal keys .applicationData (maxPlain.push 0x61))
    (fun | .plaintextTooLong _ => true | _ => false) "protected plaintext cap"
  expectRecordError
    (Record.seal keys .applicationData ByteArray.empty Record.maxInnerPlaintextLength)
    (fun | .innerPlaintextTooLong _ => true | _ => false) "inner plaintext cap"

  let tooLongHeader := encodedRecordHeader .applicationData (Record.maxCiphertextLength + 1)
  expectRecordError
    (({} : Record.Decoder).feed tooLongHeader)
    (fun | .ciphertextTooLong _ => true | _ => false) "ciphertext cap from header"
  let tooShortHeader := encodedRecordHeader .applicationData Record.aeadTagLength
  expectRecordError
    (({} : Record.Decoder).feed tooShortHeader)
    (fun | .ciphertextTooShort _ => true | _ => false) "ciphertext minimum from header"
  -- RFC 8446 §5.1: the decoder ignores TLSPlaintext.legacy_record_version
  -- (0x0301 ClientHello records are commonplace); `open` still requires
  -- 0x0303 on protected TLSCiphertext records.
  let (_, legacyRecords) ← must
    (({} : Record.Decoder).feed (ByteArray.mk #[22, 3, 1, 0, 0]))
    "legacy plaintext record version tolerated"
  expect (legacyRecords.size == 1 && legacyRecords[0]!.legacyVersion == 0x0301)
    "legacy plaintext record version was not preserved"
  let ciphertextLegacy : Record.RawRecord := {
    contentType := .applicationData
    legacyVersion := 0x0301
    fragment := bytes (Record.aeadTagLength + 1) 0
  }
  expectRecordError (Record.open keys ciphertextLegacy)
    (fun | .invalidLegacyVersion _ => true | _ => false) "legacy record version"

def clientHelloExtensions (hello : Handshake.Message) :
    Except String (Array Handshake.Extension) := do
  unless hello.msgType == Handshake.clientHelloType do
    throw "not a ClientHello"
  let reader : Handshake.Reader := { bytes := hello.body }
  let (legacyVersion, reader) ← reader.readUInt16
  unless legacyVersion == Handshake.legacyTls12Version do throw "bad legacy version"
  let (_, reader) ← reader.take 32
  let (_, reader) ← reader.readVector8
  let (cipherSuites, reader) ← reader.readVector16
  unless cipherSuites == u16 Handshake.tlsChaCha20Poly1305Sha256 do
    throw "unexpected cipher suites"
  let (compression, reader) ← reader.readVector8
  unless compression == ByteArray.mk #[0] do throw "bad compression methods"
  let (extensionBytes, reader) ← reader.readVector16
  reader.requireEnd "ClientHello"
  -- tls13-lean's own extension-block parser (proved: `parseExtensions_extensionsBytes`),
  -- so this test checks the shipped parser rather than a hand-rolled copy.
  Handshake.parseExtensions extensionBytes

def extractClientHelloShares (hello : Handshake.Message) :
    Except String (Array Handshake.ClientKeyShare) := do
  let extensions ← clientHelloExtensions hello
  let some keyShare := extensions.find? (·.extensionType == Handshake.keyShareExtension)
    | throw "missing client key_share"
  let keyReader : Handshake.Reader := { bytes := keyShare.data }
  let (shares, keyReader) ← keyReader.readVector16
  keyReader.requireEnd "client key_share extension"
  -- tls13-lean's own key_share parser (proved: `parseKeyShareEntries_keyShareEntriesBytes`
  -- and `parseKeyShareEntries_image`), so this test checks the shipped parser
  -- rather than a hand-rolled copy. Unknown/GREASE groups are retained only as
  -- identifiers, which is why the entries come back paired with the id list.
  let (_, entries) ← Handshake.parseKeyShareEntries shares
  pure entries

def extractClientHelloKey (hello : Handshake.Message) : Except String ByteArray := do
  let shares ← extractClientHelloShares hello
  let some share := shares.find? (·.group == .x25519)
    | throw "missing client x25519 share"
  unless share.keyExchange.size == 32 do throw "wrong client x25519 key length"
  pure share.keyExchange

def extractClientHelloGroups (hello : Handshake.Message) :
    Except String (Array Handshake.NamedGroup) := do
  let extensions ← clientHelloExtensions hello
  let some supportedGroups :=
      extensions.find? (·.extensionType == Handshake.supportedGroupsExtension)
    | throw "missing supported_groups"
  let reader : Handshake.Reader := { bytes := supportedGroups.data }
  let (encodedGroups, reader) ← reader.readVector16
  reader.requireEnd "supported_groups extension"
  -- tls13-lean's own uint16-vector parser (proved: `parseUInt16List_uint16ListBytes`,
  -- `parseUInt16List_image`, `parseUInt16List_injective`) plus its `knownGroups`
  -- projection, rather than a hand-rolled copy.
  let ids ← Handshake.parseUInt16List encodedGroups
  pure (Handshake.knownGroups ids.toList)

def makeServerHelloForGroup (random publicKey : ByteArray)
    (group : Handshake.NamedGroup)
    (legacySessionId : ByteArray := ByteArray.empty) : Except String Handshake.Message := do
  let extensions :=
    extension Handshake.supportedVersionsExtension (u16 Handshake.tls13Version) ++
    extension Handshake.keyShareExtension
      (u16 group.toUInt16 ++ vec16 publicKey)
  let body :=
    u16 Handshake.legacyTls12Version ++ random ++ vec8 legacySessionId ++
    u16 Handshake.tlsChaCha20Poly1305Sha256 ++ ByteArray.mk #[0] ++
    vec16 extensions
  Handshake.frame Handshake.serverHelloType body

def makeServerHello (random publicKey : ByteArray)
    (legacySessionId : ByteArray := ByteArray.empty) : Except String Handshake.Message :=
  makeServerHelloForGroup random publicKey .x25519 legacySessionId

def makeEncryptedExtensions : Except String Handshake.Message :=
  Handshake.frame Handshake.encryptedExtensionsType (vec16 ByteArray.empty)

def makeCertificateChain (certificates : Array ByteArray) :
    Except String Handshake.Message := do
  if certificates.isEmpty then
    throw "synthetic Certificate list must not be empty"
  let entries := certificates.foldl (fun result der =>
    result ++ vec24 der ++ vec16 ByteArray.empty) ByteArray.empty
  Handshake.frame Handshake.certificateType
    (vec8 ByteArray.empty ++ vec24 entries)

def makeCertificate (leaf : ByteArray) : Except String Handshake.Message :=
  makeCertificateChain #[leaf]

def makeCertificateVerify (algorithm : UInt16) (signature : ByteArray) :
    Except String Handshake.Message :=
  Handshake.frame Handshake.certificateVerifyType
    (u16 algorithm ++ vec16 signature)

def testHandshakeCodecs : IO Unit := do
  let config : Handshake.ClientHelloConfig := {
    random := bytes 32 0x11
    x25519PublicKey := bytes 32 0x22
    serverName := some "db.example.test"
  }
  let hello ← must (Handshake.encodeClientHello config) "ClientHello"
  expect (hello.msgType == Handshake.clientHelloType) "ClientHello type"
  expect (hello.encoded.extract 0 4 ==
    ByteArray.mk #[Handshake.clientHelloType] ++ u24 hello.body.size) "ClientHello frame"
  let decoded ← must (Handshake.decode hello.encoded) "ClientHello decode"
  expect (decoded == hello) "ClientHello exact encoded roundtrip"
  expect ((← must (extractClientHelloKey hello) "parse ClientHello key") ==
    config.x25519PublicKey) "ClientHello x25519 key"

  let p256Private := bytes 32 0x23
  let some p256Public := HaclStar.P256.publicKey p256Private
    | throw (IO.userError "valid deterministic P-256 scalar was rejected")
  expect (p256Public.size == 65 && p256Public.get! 0 == 4)
    "P-256 public key is not SEC1 uncompressed"
  let dualHello ← must (Handshake.encodeClientHello {
    config with p256PublicKey := some p256Public
  }) "dual-share ClientHello"
  let groups ← must (extractClientHelloGroups dualHello) "dual supported_groups"
  expect (groups == #[.x25519, .secp256r1])
    "supported_groups must advertise x25519 then secp256r1"
  let shares ← must (extractClientHelloShares dualHello) "dual key_share"
  expect (shares.size == 2 &&
    shares[0]!.group == .x25519 &&
    shares[0]!.keyExchange == config.x25519PublicKey &&
    shares[1]!.group == .secp256r1 &&
    shares[1]!.keyExchange == p256Public)
    "key_share must encode x25519 then the SEC1 P-256 point"
  match Handshake.encodeClientHello {
      config with p256PublicKey := some (bytes 65 0x05)
    } with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError "P-256 point without SEC1 0x04 prefix was accepted")

  match Handshake.encodeClientHello { config with random := bytes 31 0 } with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError "short ClientHello random accepted")
  match Handshake.encodeLength8 256 with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError "uint8 length overflow accepted")
  match Handshake.decode (ByteArray.mk #[Handshake.finishedType, 0, 0, 32, 1]) with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError "truncated handshake frame accepted")
  match Handshake.decode (hello.encoded.push 0) with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError "trailing handshake byte accepted")

  let serverPublic := bytes 32 0x44
  let serverHello ← must (makeServerHello (bytes 32 0x33) serverPublic) "make SH"
  let parsedServerHello ← must (Handshake.parseServerHello serverHello) "parse SH"
  expect (parsedServerHello.selectedGroup == .x25519 &&
    parsedServerHello.keyExchange == serverPublic) "ServerHello key extraction"
  let p256ServerHello ← must
    (makeServerHelloForGroup (bytes 32 0x34) p256Public .secp256r1)
    "make P-256 ServerHello"
  let parsedP256ServerHello ← must
    (Handshake.parseServerHello p256ServerHello) "parse P-256 ServerHello"
  expect (parsedP256ServerHello.selectedGroup == .secp256r1 &&
    parsedP256ServerHello.keyExchange == p256Public)
    "P-256 ServerHello key extraction"

  let hrrRandom := ByteArray.mk #[
    0xcf, 0x21, 0xad, 0x74, 0xe5, 0x9a, 0x61, 0x11,
    0xbe, 0x1d, 0x8c, 0x02, 0x1e, 0x65, 0xb8, 0x91,
    0xc2, 0xa2, 0x11, 0x16, 0x7a, 0xbb, 0x8c, 0x5e,
    0x07, 0x9e, 0x09, 0xe2, 0xc8, 0xa8, 0x33, 0x9c
  ]
  let hrr ← must (makeServerHello hrrRandom serverPublic) "make HRR"
  match Handshake.parseServerHello hrr with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError "HelloRetryRequest was accepted")

  let ee ← must makeEncryptedExtensions "make EE"
  let _ ← must (Handshake.parseEncryptedExtensions ee) "parse EE"
  let cert ← must (makeCertificate (ByteArray.mk #[0x30, 0x01, 0x00])) "make cert"
  let parsedCert ← must (Handshake.parseCertificate cert) "parse cert"
  expect (parsedCert.leafDer == ByteArray.mk #[0x30, 0x01, 0x00]) "leaf DER"
  let cv ← must (makeCertificateVerify Handshake.ed25519 (bytes 64 0x5a)) "make CV"
  let parsedCv ← must (Handshake.parseCertificateVerify cv) "parse CV"
  expect (parsedCv.algorithm == Handshake.ed25519 &&
    parsedCv.signature == bytes 64 0x5a) "CertificateVerify structure"
  let forbiddenCv ← must
    (makeCertificateVerify Handshake.rsaPkcs1Sha256 (bytes 256 0x5a))
    "make forbidden PKCS#1 CV"
  let parsedForbiddenCv ← must
    (Handshake.parseCertificateVerify forbiddenCv)
    "structurally parse forbidden PKCS#1 CV"
  expect (parsedForbiddenCv.algorithm == Handshake.rsaPkcs1Sha256)
    "CertificateVerify parser changed the wire scheme"

  let finished ← must (Handshake.encodeFinished (bytes 32 0x77)) "encode Finished"
  let parsedFinished ← must (Handshake.parseFinished finished) "parse Finished"
  expect (parsedFinished.verifyData == bytes 32 0x77) "Finished verify_data"
  let shortFinished ← must (Handshake.frame Handshake.finishedType (bytes 31 0))
    "short Finished"
  match Handshake.parseFinished shortFinished with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError "short Finished accepted")

  let ticketBody :=
    u32 60 ++ u32 0x12345678 ++ vec8 (ByteArray.mk #[1, 2]) ++
    vec16 (ByteArray.mk #[3, 4, 5]) ++ vec16 ByteArray.empty
  let ticket ← must (Handshake.frame Handshake.newSessionTicketType ticketBody) "make NST"
  let parsedTicket ← must (Handshake.parseNewSessionTicket ticket) "parse NST"
  expect (parsedTicket.ticketLifetime == 60 &&
    parsedTicket.ticket == ByteArray.mk #[3, 4, 5]) "NewSessionTicket structure"
  for request in [Handshake.KeyUpdateRequest.updateNotRequested,
      Handshake.KeyUpdateRequest.updateRequested] do
    let update ← must (Handshake.encodeKeyUpdate request) "encode KeyUpdate"
    let parsed ← must (Handshake.parseKeyUpdate update) "parse KeyUpdate"
    expect (parsed.request == request) "KeyUpdate roundtrip"

structure ClientDrive where
  state : Client.State
  wireBytes : ByteArray := ByteArray.empty
  plaintext : ByteArray := ByteArray.empty

def driveClientChunks (initial : Client.State) (wire : ByteArray) (chunkSize : Nat) :
    Except Client.Error ClientDrive := do
  let mut state := initial
  let mut outbound := ByteArray.empty
  let mut plaintext := ByteArray.empty
  let mut offset := 0
  let chunkSize := max chunkSize 1
  while offset < wire.size do
    let stop := min wire.size (offset + chunkSize)
    let output ← Client.feed state (wire.extract offset stop)
    state := output.state
    outbound := outbound ++ output.wireBytes
    plaintext := plaintext ++ output.plaintext
    offset := stop
  pure { state, wireBytes := outbound, plaintext }

def decodeRecords (wire : ByteArray) : IO (Array Record.RawRecord) := do
  let (decoder, records) ← must (({} : Record.Decoder).feed wire) "decode record stream"
  expect decoder.buffered.isEmpty "record stream ended with a partial record"
  pure records

def tlsFinishedVerifyData (trafficSecret transcript : ByteArray) : ByteArray :=
  let finishedKey := TLS13.KeySchedule.expandLabel trafficSecret "finished"
    ByteArray.empty TLS13.KeySchedule.hashLen
  HaclStar.hmacSha256 finishedKey (HaclStar.sha256 transcript)

structure CertificateVerifyVector where
  name : String
  certificatePath : String
  algorithm : UInt16
  expectedTranscriptHashHex : String
  signatureHex : String

def rsaCertificateVerifyVector : CertificateVerifyVector := {
  name := "RSA-PSS-RSAE"
  certificatePath := "Test/Fixtures/TlsCertificateVerify/rsa.pem"
  algorithm := Handshake.rsaPssRsaeSha256
  expectedTranscriptHashHex :=
    "368c513aa3d01a41d9fc4a8da5719b1a97d7dde25a08dc99f43637239d36ba82"
  signatureHex :=
    "47438834ee11a837b4003b33a946b3aeb588978a5c1b244161fba3f6aa8859d6" ++
    "912d6e8c5f5cfeac949c29d5207a5dc4e5b6333842016156f5627f6b7775933a" ++
    "b7f4f08772441415c64860b27cfa84765d5ce5035dc8ad16d60d72de1f18ca34" ++
    "9f7e76dddff7616b5d2e4505866da4ef55bdaf471737adca311e050e00f5e233c" ++
    "73db9ee540aa5179d80e4ac2ce28ab1a768bf84f2e185cab324857ba3f936ca65" ++
    "13836074d6de48e3ce04df94aade9bce9b69936ec0fd3dd277e6af947c99eb760" ++
    "2d5007d600fe8c89d01f0a7cf0142c967555e8459f2446c6d1f12e12692a55b6" ++
    "3f17f05109892cc1478165f1d7b2b58c7c0d8fe92c4d6dd68b3062780f177"
}

def p256CertificateVerifyVector : CertificateVerifyVector := {
  name := "ECDSA-P256"
  certificatePath := "Test/Fixtures/TlsCertificateVerify/p256.pem"
  algorithm := Handshake.ecdsaSecp256r1Sha256
  expectedTranscriptHashHex :=
    "bb2c338022742ce6e43e99f959f18a3a69b22510654c139069d2b159dc7fb866"
  signatureHex :=
    "3046022100be8664214c5f50bed8bea249cd122e896d400af8f6bd9979762eeb9c" ++
    "32fde1b0022100a03da6a3b5d0a16ffc282c002159eb69c051faa1f1ec902e907" ++
    "68f05eb3b5594"
}

def ed25519CertificateVerifyVector : CertificateVerifyVector := {
  name := "Ed25519"
  certificatePath := "Test/Fixtures/TlsCertificateVerify/ed25519.pem"
  algorithm := Handshake.ed25519
  expectedTranscriptHashHex :=
    "3352d1586a02a02145b4a28363fbb06a520b69ee6496df910a53f844b0010958"
  signatureHex :=
    "63fde6a0c6a018f241f25d163c006ee4e8b1f619a0ff9d19cd2893707d41e73b" ++
    "86f9cacc969c4f255dd412dd5dc24cc4460643d8fbc6147adb45cb496874c701"
}

def ed25519EmptySessionIdVector : CertificateVerifyVector :=
  { ed25519CertificateVerifyVector with
    name := "Ed25519-empty-session-id"
    expectedTranscriptHashHex :=
      "a40e84207b92becf29dbfe44f55a2991d81960413db3ae6899c695f8cb2ca873"
    signatureHex :=
      "d1259cb7c9df4f9b92f87cd506a240e8ed04a6b9b7edeaf1b347a7e3bdb5a83" ++
      "d21eafb66fcab02563350bf507679dae4a2b8c27d5080518be1e395f054f4260c"
  }

def ed25519P256KeyExchangeVector : CertificateVerifyVector :=
  { ed25519CertificateVerifyVector with
    name := "Ed25519-P256-key-exchange"
    expectedTranscriptHashHex :=
      "d9ca90f7686b9d776991ee32eaca1c769f1177ffe0557ac59c5c48e446a2224b"
    signatureHex :=
      "136ca2c5875875b9b4ec7a2acc2474515f573aaa29341792063504f0aa95f43c" ++
      "3fb1b9ef6d462b0d94c7a8f536c1ce815060f3c1ae0fd1b1823cd75137953301"
  }

inductive CertificateVerifyMode where
  | valid
  | tamperedSignature
  | scheme (algorithm : UInt16)
  | omitted

def readCertificateDER (path : String) : IO ByteArray := do
  let text ← IO.FS.readFile path
  let certificates ← must (TLS13.X509.Certificate.decodePEM text) path
  expect (certificates.size == 1) s!"{path}: expected exactly one certificate"
  pure certificates[0]!.encoded

def vectorSignature (vector : CertificateVerifyVector) : IO ByteArray := do
  let some signature := Pg.Crypto.ofHex? vector.signatureHex
    | throw (IO.userError s!"{vector.name}: malformed signature hex")
  expect (!signature.isEmpty) s!"{vector.name}: signature fixture is empty"
  pure signature

structure SyntheticPeer where
  selectedGroup : Handshake.NamedGroup
  initialState : Client.State
  serverHelloWire : ByteArray
  stateAfterServerHello : Client.State
  encryptedFlight : ByteArray
  clientHello : Handshake.Message
  serverHello : Handshake.Message
  encryptedExtensions : Handshake.Message
  certificate : Handshake.Message
  certificateVerify? : Option Handshake.Message
  serverFinished : Handshake.Message
  transcriptThroughServerFinished : ByteArray
  clientHandshakeKeys : Record.TrafficKeys
  serverHandshakeKeys : Record.TrafficKeys
  clientApplicationKeys : Record.TrafficKeys
  serverApplicationKeys : Record.TrafficKeys
  leafCertificate : ByteArray

def prepareSyntheticPeer (chunkSize : Nat) (badFinished : Bool := false)
    (legacySessionId : ByteArray := bytes 8 0xa5)
    (selectedGroup : Handshake.NamedGroup := .x25519)
    (certificateVerifyVector : CertificateVerifyVector :=
      ed25519CertificateVerifyVector)
    (certificateVerifyMode : CertificateVerifyMode := .valid) :
    IO SyntheticPeer := do
  let clientPrivate := bytes 32 0x17
  let clientP256Private :=
    if selectedGroup == .secp256r1 then some (bytes 32 0x23) else none
  let started ← must (Client.start {
    clientRandom := bytes 32 0x21
    x25519Private := clientPrivate
    p256Private := clientP256Private
    legacySessionId
    serverName := some "db.example.test"
  }) "start TLS client"
  let clientRecords ← decodeRecords started.wireBytes
  expect (clientRecords.size == 1 &&
    clientRecords[0]!.contentType == .handshake) "initial ClientHello record"
  let clientHello ← must (Handshake.decode clientRecords[0]!.fragment)
    "decode emitted ClientHello"
  let clientShares ← must (extractClientHelloShares clientHello) "client key shares"
  let some selectedClientShare := clientShares.find? (·.group == selectedGroup)
    | throw (IO.userError s!"ClientHello omitted {repr selectedGroup} key share")
  match selectedGroup with
  | .x25519 =>
    expect (selectedClientShare.keyExchange == HaclStar.X25519.base clientPrivate)
      "ClientHello x25519 public key does not match private scalar"
  | .secp256r1 =>
    let some privateKey := clientP256Private
      | throw (IO.userError "synthetic client P-256 private key missing")
    let some expectedPublic := HaclStar.P256.publicKey privateKey
      | throw (IO.userError "synthetic client P-256 scalar rejected")
    expect (clientShares.map (·.group) == #[.x25519, .secp256r1] &&
      selectedClientShare.keyExchange == expectedPublic)
      "ClientHello P-256 share/order does not match private scalar"

  let serverPrivate := if selectedGroup == .x25519 then bytes 32 0x39 else bytes 32 0x4b
  let serverPublic ← match selectedGroup with
    | .x25519 => pure (HaclStar.X25519.base serverPrivate)
    | .secp256r1 =>
      let some publicKey := HaclStar.P256.publicKey serverPrivate
        | throw (IO.userError "synthetic server P-256 scalar rejected")
      pure publicKey
  let serverHello ← must
    (makeServerHelloForGroup (bytes 32 0x31) serverPublic selectedGroup legacySessionId)
    "make ServerHello"
  let serverHelloWire ← must
    (Record.encodePlaintext .handshake serverHello.encoded) "frame ServerHello record"
  let afterServerHello ← must
    (driveClientChunks started.state serverHelloWire chunkSize) "feed ServerHello"
  expect (afterServerHello.state.phase == .waitingEncryptedExtensions)
    "client did not install handshake keys after ServerHello"
  expect (afterServerHello.wireBytes.isEmpty && afterServerHello.plaintext.isEmpty)
    "ServerHello produced output"

  let sharedSecret ← match selectedGroup with
    | .x25519 =>
      let some secret := HaclStar.X25519.ecdh serverPrivate selectedClientShare.keyExchange
        | throw (IO.userError "synthetic server X25519 failed")
      pure secret
    | .secp256r1 =>
      let some secret := HaclStar.P256.ecdh serverPrivate selectedClientShare.keyExchange
        | throw (IO.userError "synthetic server P-256 ECDH failed")
      pure secret
  let emptyHash := HaclStar.sha256 ByteArray.empty
  let earlySecret := TLS13.KeySchedule.earlySecret
  let handshakeSecret :=
    TLS13.KeySchedule.handshakeSecret earlySecret sharedSecret emptyHash
  let helloTranscript := clientHello.encoded ++ serverHello.encoded
  let helloHash := HaclStar.sha256 helloTranscript
  let clientHandshakeSecret :=
    TLS13.KeySchedule.deriveSecret handshakeSecret "c hs traffic" helloHash
  let serverHandshakeSecret :=
    TLS13.KeySchedule.deriveSecret handshakeSecret "s hs traffic" helloHash
  let clientHandshakeKeys ← must
    (Record.deriveTrafficKeys clientHandshakeSecret) "client handshake keys"
  let serverHandshakeKeys ← must
    (Record.deriveTrafficKeys serverHandshakeSecret) "server handshake keys"

  let encryptedExtensions ← must makeEncryptedExtensions "make EncryptedExtensions"
  let leafCertificate ← readCertificateDER certificateVerifyVector.certificatePath
  let certificate ← must (makeCertificate leafCertificate) "make Certificate"
  let transcriptThroughCertificate :=
    helloTranscript ++ encryptedExtensions.encoded ++ certificate.encoded
  let transcriptHash := HaclStar.sha256 transcriptThroughCertificate
  expect
    (Pg.Crypto.toHexLower transcriptHash ==
      certificateVerifyVector.expectedTranscriptHashHex)
    s!"{certificateVerifyVector.name}: synthetic transcript changed"
  let fixtureSignature ← vectorSignature certificateVerifyVector
  let signature :=
    match certificateVerifyMode with
    | .tamperedSignature =>
      fixtureSignature.set! (fixtureSignature.size / 2)
        (fixtureSignature.get! (fixtureSignature.size / 2) ^^^ 0x01)
    | _ => fixtureSignature
  let algorithm :=
    match certificateVerifyMode with
    | .scheme algorithm => algorithm
    | _ => certificateVerifyVector.algorithm
  let certificateVerify? ←
    match certificateVerifyMode with
    | .omitted => pure none
    | _ =>
      some <$> must (makeCertificateVerify algorithm signature)
        "make CertificateVerify"
  let beforeServerFinished :=
    match certificateVerify? with
    | some certificateVerify =>
      transcriptThroughCertificate ++ certificateVerify.encoded
    | none => transcriptThroughCertificate
  let correctVerifyData :=
    tlsFinishedVerifyData serverHandshakeSecret beforeServerFinished
  let verifyData :=
    if badFinished then
      correctVerifyData.set! 0 (correctVerifyData.get! 0 ^^^ 1)
    else
      correctVerifyData
  let serverFinished ← must (Handshake.encodeFinished verifyData) "make server Finished"
  let transcriptThroughServerFinished := beforeServerFinished ++ serverFinished.encoded
  let protectedHandshake :=
    encryptedExtensions.encoded ++ certificate.encoded ++
      (certificateVerify?.map (·.encoded)).getD ByteArray.empty ++
      serverFinished.encoded
  -- Coalesce all four encrypted handshake messages in one record. A dummy
  -- server CCS immediately before it exercises compatibility mode as well.
  let (_, protectedWire) ← must
    (Record.seal serverHandshakeKeys .handshake protectedHandshake)
    "seal synthetic server flight"
  let ccs ← must
    (Record.encodePlaintext .changeCipherSpec (ByteArray.mk #[1])) "server CCS"
  let encryptedFlight := ccs ++ protectedWire

  let masterSecret := TLS13.KeySchedule.masterSecret handshakeSecret emptyHash
  let applicationHash := HaclStar.sha256 transcriptThroughServerFinished
  let clientApplicationSecret :=
    TLS13.KeySchedule.deriveSecret masterSecret "c ap traffic" applicationHash
  let serverApplicationSecret :=
    TLS13.KeySchedule.deriveSecret masterSecret "s ap traffic" applicationHash
  let clientApplicationKeys ← must
    (Record.deriveTrafficKeys clientApplicationSecret) "client application keys"
  let serverApplicationKeys ← must
    (Record.deriveTrafficKeys serverApplicationSecret) "server application keys"

  pure {
    selectedGroup
    initialState := started.state
    serverHelloWire
    stateAfterServerHello := afterServerHello.state
    encryptedFlight
    clientHello
    serverHello
    encryptedExtensions
    certificate
    certificateVerify?
    serverFinished
    transcriptThroughServerFinished
    clientHandshakeKeys
    serverHandshakeKeys
    clientApplicationKeys
    serverApplicationKeys
    leafCertificate
  }

def completeSyntheticHandshake (chunkSize : Nat)
    (legacySessionId : ByteArray := bytes 8 0xa5)
    (selectedGroup : Handshake.NamedGroup := .x25519)
    (certificateVerifyVector : CertificateVerifyVector :=
      ed25519CertificateVerifyVector) :
    IO (SyntheticPeer × Client.State) := do
  let peer ← prepareSyntheticPeer chunkSize false legacySessionId selectedGroup
    certificateVerifyVector
  let connected ← must
    (driveClientChunks peer.stateAfterServerHello peer.encryptedFlight chunkSize)
    s!"feed encrypted server flight/{chunkSize}"
  expect connected.state.connected s!"client did not connect under {chunkSize}-byte fragmentation"
  expect connected.plaintext.isEmpty "handshake surfaced application plaintext"
  expect (connected.state.leafCertificate? == some peer.leafCertificate)
    "client did not retain the leaf certificate"
  expect (connected.state.peerCertificates.size == 1 &&
    connected.state.peerCertificates[0]!.encoded == peer.leafCertificate)
    "client did not retain the strict-parsed Certificate list"

  let clientRecords ← decodeRecords connected.wireBytes
  let encryptedFinished ←
    if legacySessionId.isEmpty then do
      expect (clientRecords.size == 1) "empty-SID client flight should contain only Finished"
      pure clientRecords[0]!
    else do
      expect (clientRecords.size == 2) "compatibility client flight should contain CCS + Finished"
      expect (clientRecords[0]!.contentType == .changeCipherSpec &&
        clientRecords[0]!.fragment == ByteArray.mk #[1]) "client compatibility CCS"
      pure clientRecords[1]!
  expect (encryptedFinished.contentType == .applicationData)
    "client Finished was not protected"
  let (_, finishedPlaintext) ← must
    (Record.open peer.clientHandshakeKeys encryptedFinished) "decrypt client Finished"
  expect (finishedPlaintext.contentType == .handshake) "client Finished inner type"
  let finishedMessage ← must
    (Handshake.decode finishedPlaintext.fragment) "decode client Finished"
  let finished ← must (Handshake.parseFinished finishedMessage) "parse client Finished"
  let expectedVerifyData :=
    tlsFinishedVerifyData peer.clientHandshakeKeys.secret
      peer.transcriptThroughServerFinished
  expect (finished.verifyData == expectedVerifyData) "client Finished verify_data"
  expect (connected.state.transcript.isEmpty &&
    connected.state.x25519Private.isEmpty &&
    connected.state.p256Private.isNone &&
    connected.state.leafPublicKey?.isNone &&
    connected.state.handshakeSecret?.isNone &&
    connected.state.clientHandshakeTrafficSecret?.isNone &&
    connected.state.serverHandshakeTrafficSecret?.isNone)
    "client retained obsolete handshake secrets"
  pure (peer, connected.state)

def testSyntheticHandshake : IO Unit := do
  -- The server flight is record-coalesced internally, then each complete
  -- exchange is driven under hostile TCP fragmentation.
  for chunkSize in [1, 3, 7, 65536] do
    discard <| completeSyntheticHandshake chunkSize
  -- Zero-length session IDs deliberately opt out of compatibility CCS.
  discard <| completeSyntheticHandshake 5 ByteArray.empty .x25519
    ed25519EmptySessionIdVector

  let badPeer ← prepareSyntheticPeer 3 true
  match driveClientChunks badPeer.stateAfterServerHello badPeer.encryptedFlight 3 with
  | .error .finishedMismatch => pure ()
  | .error error => throw (IO.userError s!"bad Finished: unexpected error {error}")
  | .ok _ => throw (IO.userError "bad server Finished was accepted")

def testCertificateVerify : IO Unit := do
  let sessionId := bytes 8 0xa5
  -- Each captured OpenSSL signature covers the deterministic raw synthetic
  -- transcript through Certificate. Completion proves the engine dispatches
  -- on the wire scheme and the leaf SPKI for all three supported key types.
  for vector in [
      rsaCertificateVerifyVector,
      p256CertificateVerifyVector,
      ed25519CertificateVerifyVector
    ] do
    let (_, connected) ←
      completeSyntheticHandshake 3 sessionId .x25519 vector
    expect connected.connected s!"{vector.name}: CertificateVerify handshake"

  let tampered ← prepareSyntheticPeer 3 false sessionId .x25519
    ed25519CertificateVerifyVector .tamperedSignature
  match driveClientChunks tampered.stateAfterServerHello tampered.encryptedFlight 3 with
  | .error .certificateVerifyFailed => pure ()
  | .error error =>
    throw (IO.userError s!"tampered CertificateVerify: unexpected error {error}")
  | .ok _ => throw (IO.userError "tampered CertificateVerify was accepted")
  let coalescedFailure ←
    match Client.feedWithFailure tampered.initialState
        (tampered.serverHelloWire ++ tampered.encryptedFlight) with
    | .error failure =>
      match failure.error with
      | .certificateVerifyFailed => pure failure
      | error =>
        throw (IO.userError
          s!"coalesced tampered CertificateVerify: unexpected error {error}")
    | .ok _ =>
      throw (IO.userError
        "coalesced ServerHello/tampered CertificateVerify was accepted")
  expect coalescedFailure.state.writeKeys?.isSome
    "coalesced CertificateVerify failure lost handshake write keys"
  expect
    (Client.Error.fatalAlertDescription? .certificateVerifyFailed == some 51)
    "CertificateVerify failure did not map to decrypt_error"
  let fatalAlert ← must
    (Client.sealFatalAlert coalescedFailure.state 51)
    "seal CertificateVerify decrypt_error"
  let fatalRecords ← decodeRecords fatalAlert.wireBytes
  expect (fatalRecords.size == 1) "fatal alert record count"
  let (_, fatalPlaintext) ← must
    (Record.open tampered.clientHandshakeKeys fatalRecords[0]!)
    "open CertificateVerify decrypt_error"
  expect (fatalPlaintext.contentType == .alert &&
    fatalPlaintext.fragment == ByteArray.mk #[2, 51])
    "CertificateVerify failure alert payload"

  let mismatch ← prepareSyntheticPeer 3 false sessionId .x25519
    ed25519CertificateVerifyVector
    (.scheme Handshake.ecdsaSecp256r1Sha256)
  match driveClientChunks mismatch.stateAfterServerHello mismatch.encryptedFlight 3 with
  | .error (.certificateVerifySchemeMismatch algorithm) =>
    expect (algorithm == Handshake.ecdsaSecp256r1Sha256)
      "scheme/key mismatch reported the wrong algorithm"
  | .error error =>
    throw (IO.userError s!"scheme/key mismatch: unexpected error {error}")
  | .ok _ => throw (IO.userError "CertificateVerify scheme/key mismatch was accepted")
  expect
    (Client.Error.fatalAlertDescription?
      (.certificateVerifySchemeMismatch Handshake.ecdsaSecp256r1Sha256) ==
        some 47)
    "CertificateVerify scheme mismatch did not map to illegal_parameter"

  let forbidden ← prepareSyntheticPeer 3 false sessionId .x25519
    rsaCertificateVerifyVector (.scheme Handshake.rsaPkcs1Sha256)
  match driveClientChunks forbidden.stateAfterServerHello forbidden.encryptedFlight 3 with
  | .error (.certificateVerifySchemeMismatch algorithm) =>
    expect (algorithm == Handshake.rsaPkcs1Sha256)
      "PKCS#1 CertificateVerify reported the wrong algorithm"
  | .error error =>
    throw (IO.userError s!"PKCS#1 CertificateVerify: unexpected error {error}")
  | .ok _ => throw (IO.userError "TLS 1.3 PKCS#1 CertificateVerify was accepted")

  let omitted ← prepareSyntheticPeer 3 false sessionId .x25519
    ed25519CertificateVerifyVector .omitted
  match driveClientChunks omitted.stateAfterServerHello omitted.encryptedFlight 3 with
  | .error (.unexpectedHandshake .waitingCertificateVerify actual) =>
    expect (actual == Handshake.finishedType)
      "missing CertificateVerify reported the wrong next message"
  | .error error =>
    throw (IO.userError s!"missing CertificateVerify: unexpected error {error}")
  | .ok _ => throw (IO.userError "missing CertificateVerify was accepted")
  expect
    (Client.Error.fatalAlertDescription?
      (.unexpectedHandshake .waitingCertificateVerify Handshake.finishedType) ==
        some 10)
    "missing CertificateVerify did not map to unexpected_message"

def testCertificateListRetention : IO Unit := do
  let peer ← prepareSyntheticPeer 3
  let certificate ← must
    (makeCertificateChain #[peer.leafCertificate, peer.leafCertificate])
    "make two-entry Certificate"
  let (_, wire) ← must
    (Record.seal peer.serverHandshakeKeys .handshake
      (peer.encryptedExtensions.encoded ++ certificate.encoded))
    "seal two-entry Certificate flight"
  let waiting ← must
    (driveClientChunks peer.stateAfterServerHello wire 2)
    "feed two-entry Certificate flight"
  expect (waiting.state.phase == .waitingCertificateVerify &&
    waiting.state.peerCertificates.size == 2 &&
    waiting.state.peerCertificates[0]!.encoded == peer.leafCertificate &&
    waiting.state.peerCertificates[1]!.encoded == peer.leafCertificate)
    "client did not strict-parse and retain every Certificate-list entry"

  let malformedCertificate ← must
    (makeCertificateChain #[
      peer.leafCertificate,
      ByteArray.mk #[0x30, 0x01, 0x00]
    ])
    "make malformed-intermediate Certificate"
  let (_, malformedWire) ← must
    (Record.seal peer.serverHandshakeKeys .handshake
      (peer.encryptedExtensions.encoded ++ malformedCertificate.encoded))
    "seal malformed-intermediate Certificate flight"
  match driveClientChunks peer.stateAfterServerHello malformedWire 2 with
  | .error (.badCertificate _) => pure ()
  | .error error =>
    throw (IO.userError s!"malformed intermediate: unexpected error {error}")
  | .ok _ =>
    throw (IO.userError "malformed intermediate certificate was retained")

def testP256Client : IO Unit := do
  let sessionId := bytes 8 0xb6
  let (peer, connectedState) ←
    completeSyntheticHandshake 3 sessionId .secp256r1
      ed25519P256KeyExchangeVector
  expect (peer.selectedGroup == .secp256r1 && connectedState.connected)
    "P-256 synthetic handshake did not connect"
  let payload := "P-256 application traffic".toUTF8
  let (_, wire) ← must
    (Record.seal peer.serverApplicationKeys .applicationData payload)
    "seal P-256 server application data"
  let received ← must (driveClientChunks connectedState wire 1)
    "feed P-256 application data"
  expect (received.plaintext == payload)
    "P-256 application traffic keys disagree"

  -- The SEC1 shape is valid, so the handshake codec accepts it; (0,0) is not
  -- on P-256, and the ECDH primitive must reject it before any key is derived.
  let clientStarted ← must (Client.start {
    clientRandom := bytes 32 0x61
    x25519Private := bytes 32 0x17
    p256Private := some (bytes 32 0x23)
    legacySessionId := sessionId
  }) "start bad-point P-256 client"
  let invalidPoint := (ByteArray.empty.push 4) ++ bytes 64 0
  let invalidHello ← must
    (makeServerHelloForGroup (bytes 32 0x62) invalidPoint .secp256r1 sessionId)
    "make off-curve P-256 ServerHello"
  let parsedInvalid ← must (Handshake.parseServerHello invalidHello)
    "structurally parse off-curve P-256 ServerHello"
  expect (parsedInvalid.selectedGroup == .secp256r1)
    "off-curve fixture did not select P-256"
  let invalidWire ← must
    (Record.encodePlaintext .handshake invalidHello.encoded)
    "frame off-curve P-256 ServerHello"
  match Client.feed clientStarted.state invalidWire with
  | .error .keyExchangeFailed => pure ()
  | .error error =>
    throw (IO.userError s!"off-curve P-256 point: unexpected error {error}")
  | .ok _ => throw (IO.userError "off-curve P-256 ServerHello was accepted")

def testApplicationAndPostHandshake : IO Unit := do
  let (peer, connectedState) ← completeSyntheticHandshake 3

  let serverPayload := "server application bytes".toUTF8
  let (serverKeys, serverWire) ← must
    (Record.seal peer.serverApplicationKeys .applicationData serverPayload)
    "seal server application data"
  let received ← must (driveClientChunks connectedState serverWire 2)
    "feed server application data"
  expect (received.plaintext == serverPayload && received.wireBytes.isEmpty)
    "server application roundtrip"

  let clientPayload := "client application bytes".toUTF8
  let sent ← must (Client.sealApplication received.state clientPayload)
    "seal client application data"
  let sentRecords ← decodeRecords sent.wireBytes
  expect (sentRecords.size == 1) "small client write record count"
  let (peerClientReadKeys, clientPlaintext) ← must
    (Record.open peer.clientApplicationKeys sentRecords[0]!)
    "open client application data"
  expect (clientPlaintext.contentType == .applicationData &&
    clientPlaintext.fragment == clientPayload) "client application roundtrip"

  let expectedLargeChunks := #[
    bytes Record.maxPlaintextLength 0x41,
    bytes Record.maxPlaintextLength 0x42,
    ByteArray.mk #[0x43]
  ]
  let largePayload := expectedLargeChunks.foldl (· ++ ·) ByteArray.empty
  let largeSent ← must (Client.sealApplication sent.state largePayload)
    "seal split client application data"
  let largeRecords ← decodeRecords largeSent.wireBytes
  expect (largeRecords.size == 3)
    s!"32769-byte client write produced {largeRecords.size} records, expected 3"
  let mut peerClientReadKeys := peerClientReadKeys
  let mut openedLarge := ByteArray.empty
  for i in [0:largeRecords.size] do
    let (nextKeys, plaintext) ← must
      (Record.open peerClientReadKeys largeRecords[i]!)
      s!"open split client application record {i}"
    peerClientReadKeys := nextKeys
    expect (plaintext.contentType == .applicationData &&
      plaintext.fragment == expectedLargeChunks[i]!)
      s!"split client application record {i} length/order"
    openedLarge := openedLarge ++ plaintext.fragment
  expect (openedLarge == largePayload)
    "split client application records did not decrypt in order"

  let ticketBody :=
    u32 120 ++ u32 0x87654321 ++ vec8 (ByteArray.mk #[9]) ++
    vec16 (ByteArray.mk #[8, 7, 6]) ++ vec16 ByteArray.empty
  let ticket ← must
    (Handshake.frame Handshake.newSessionTicketType ticketBody) "post-handshake NST"
  let (serverKeys, ticketWire) ← must
    (Record.seal serverKeys .handshake ticket.encoded) "seal NST"
  let afterTicket ← must (driveClientChunks largeSent.state ticketWire 4) "feed NST"
  expect (afterTicket.state.connected && afterTicket.plaintext.isEmpty &&
    afterTicket.wireBytes.isEmpty) "NewSessionTicket handling"

  let keyUpdate ← must
    (Handshake.encodeKeyUpdate .updateRequested) "server KeyUpdate"
  let (oldServerKeys, updateWire) ← must
    (Record.seal serverKeys .handshake keyUpdate.encoded) "seal KeyUpdate"
  let updatedServerKeys ← must oldServerKeys.update "update server write keys"
  let afterUpdate ← must
    (driveClientChunks afterTicket.state updateWire 1) "feed KeyUpdate"
  expect (!afterUpdate.wireBytes.isEmpty && afterUpdate.plaintext.isEmpty)
    "requested KeyUpdate did not produce a response"
  let updateResponseRecords ← decodeRecords afterUpdate.wireBytes
  expect (updateResponseRecords.size == 1) "KeyUpdate response record count"
  let (oldPeerClientReadKeys, updatePlaintext) ← must
    (Record.open peerClientReadKeys updateResponseRecords[0]!)
    "open KeyUpdate response"
  expect (updatePlaintext.contentType == .handshake) "KeyUpdate response inner type"
  let updateResponse ← must
    (Handshake.decode updatePlaintext.fragment) "decode KeyUpdate response"
  let parsedUpdate ← must
    (Handshake.parseKeyUpdate updateResponse) "parse KeyUpdate response"
  expect (parsedUpdate.request == .updateNotRequested) "KeyUpdate response value"
  let updatedPeerClientReadKeys ← must oldPeerClientReadKeys.update
    "update peer client-read keys"

  let closeAlert := ByteArray.mk #[1, 0]
  let (_, closeWire) ← must
    (Record.seal updatedServerKeys .alert closeAlert) "seal peer close_notify"
  let closed ← must (driveClientChunks afterUpdate.state closeWire 2) "feed close_notify"
  expect closed.state.closed "close_notify exchange did not close both directions"
  let closeResponseRecords ← decodeRecords closed.wireBytes
  expect (closeResponseRecords.size == 1) "close_notify response record count"
  let (_, closePlaintext) ← must
    (Record.open updatedPeerClientReadKeys closeResponseRecords[0]!)
    "open close_notify response"
  expect (closePlaintext.contentType == .alert &&
    closePlaintext.fragment == closeAlert) "close_notify response"
  let repeated ← must (Client.closeNotify closed.state) "repeat close_notify"
  expect repeated.wireBytes.isEmpty "repeated close_notify was not idempotent"

def main : IO Unit := do
  testRecordFraming
  testRecordProtection
  testRecordLimits
  testHandshakeCodecs
  testSyntheticHandshake
  testCertificateVerify
  testCertificateListRetention
  testP256Client
  testApplicationAndPostHandshake
  IO.println "all TLS record/handshake/client assertions passed"
