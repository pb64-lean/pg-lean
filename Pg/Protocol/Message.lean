module

import Std.Tactic.BVDecide
public meta import Std.Tactic.BVDecide.Reflect

public section

namespace Pg
namespace Protocol

/-!
PostgreSQL frontend/backend wire protocol, version 3.0: byte-level message
framing. Every message after the startup phase is `tag (1 byte)` followed by a
big-endian `Int32` length that counts itself and the payload (but not the tag).
Startup-phase frontend messages (StartupMessage, SSLRequest, CancelRequest)
omit the tag byte.

This layer deals only in raw framed messages (`RawMessage`) and incremental
decoding of a TCP byte stream (`DecodeState`); typed message
encoding/decoding builds on top of it.
-/

def protocolVersion : UInt32 := 196608  -- 3.0

/-- Protocol 3.2 (PostgreSQL 18+): variable-length cancel keys. 3.1 was never
used (skipped due to a pgbouncer negotiation bug). -/
def protocolVersion32 : UInt32 := 196610

def sslRequestCode : UInt32 := 80877103

def cancelRequestCode : UInt32 := 80877102

/-- Length prefix counts itself (4 bytes) but not the tag byte. -/
def lengthFieldSize : Nat := 4

/-- Sanity cap on a single message body; PostgreSQL itself enforces ~1 GiB. -/
def maxMessageLength : Nat := 1 <<< 30

-- Big-endian primitive writers, appending to an accumulator ByteArray.

def putUInt16 (out : ByteArray) (v : UInt16) : ByteArray :=
  (out.push (v >>> 8).toUInt8).push v.toUInt8

def putUInt32 (out : ByteArray) (v : UInt32) : ByteArray :=
  let out := out.push (v >>> 24).toUInt8
  let out := out.push (v >>> 16).toUInt8
  let out := out.push (v >>> 8).toUInt8
  out.push v.toUInt8

def putInt32 (out : ByteArray) (v : Int32) : ByteArray :=
  putUInt32 out v.toUInt32

/-- Null-terminated string, the protocol's only string representation. -/
def putCString (out : ByteArray) (s : String) : ByteArray :=
  (out ++ s.toUTF8).push 0

-- Big-endian primitive readers over a ByteArray at an offset. Bounds are the
-- caller's responsibility only in the sense that failures are `none`.

def getUInt16? (bytes : ByteArray) (off : Nat) : Option UInt16 :=
  if off + 2 ≤ bytes.size then
    some ((bytes.get! off).toUInt16 <<< 8 ||| (bytes.get! (off + 1)).toUInt16)
  else none

def getUInt32? (bytes : ByteArray) (off : Nat) : Option UInt32 :=
  if off + 4 ≤ bytes.size then
    some <|
      (bytes.get! off).toUInt32 <<< 24 |||
      (bytes.get! (off + 1)).toUInt32 <<< 16 |||
      (bytes.get! (off + 2)).toUInt32 <<< 8 |||
      (bytes.get! (off + 3)).toUInt32
  else none

def getInt32? (bytes : ByteArray) (off : Nat) : Option Int32 :=
  (getUInt32? bytes off).map (·.toInt32)

/-- Reads a null-terminated UTF-8 string starting at `off`; returns the string
and the offset just past the terminator. -/
def getCString? (bytes : ByteArray) (off : Nat) : Option (String × Nat) := do
  let rec findNul (i : Nat) : Option Nat :=
    if h : i < bytes.size then
      if bytes.get! i == 0 then some i else findNul (i + 1)
    else none
  termination_by bytes.size - i
  let nul ← findNul off
  let s ← String.fromUTF8? (bytes.extract off nul)
  pure (s, nul + 1)

/-- A framed protocol message: one tag byte plus the length-delimited payload
(the payload excludes the length field itself). -/
structure RawMessage where
  tag : UInt8
  payload : ByteArray := ByteArray.empty
  deriving Inhabited

namespace RawMessage

def encode (msg : RawMessage) : ByteArray :=
  let out := ByteArray.empty.push msg.tag
  let out := putUInt32 out (msg.payload.size + lengthFieldSize).toUInt32
  out ++ msg.payload

end RawMessage

/-- Startup-phase messages carry no tag: just `length (incl. itself) ++ payload`. -/
def encodeUntagged (payload : ByteArray) : ByteArray :=
  putUInt32 ByteArray.empty (payload.size + lengthFieldSize).toUInt32 ++ payload

/-- The StartupMessage: protocol version then `key\0value\0` pairs and a final
terminator byte. -/
def encodeStartup (params : Array (String × String))
    (version : UInt32 := protocolVersion) : ByteArray :=
  let body := putUInt32 ByteArray.empty version
  let body := params.foldl (fun acc (kv : String × String) =>
    putCString (putCString acc kv.1) kv.2) body
  encodeUntagged (body.push 0)

def encodeSSLRequest : ByteArray :=
  encodeUntagged (putUInt32 ByteArray.empty sslRequestCode)

/-- The secret key is 4 bytes under protocol 3.0 and variable-length (≤ 256
bytes) under 3.2; either way the wire format is `code ++ pid ++ secret`. -/
def encodeCancelRequest (processId : UInt32) (secretKey : ByteArray) : ByteArray :=
  encodeUntagged
    (putUInt32 (putUInt32 ByteArray.empty cancelRequestCode) processId ++ secretKey)

/-- Incremental decoder for the (tagged) message stream a client receives from
the backend. Feed TCP chunks with `decodeChunk`; complete messages accumulate
in `messages`. -/
structure DecodeState where
  buffered : ByteArray := ByteArray.empty
  messages : Array RawMessage := #[]
  deriving Inhabited

private def parseBuffered (buffered : ByteArray) (messages : Array RawMessage) :
    Except String DecodeState :=
  if buffered.size < 1 + lengthFieldSize then
    pure { buffered, messages }
  else
    match getUInt32? buffered 1 with
    | none => pure { buffered, messages }
    | some len32 =>
      let tag := buffered.get! 0
      let len := len32.toNat
      if hlen : len < lengthFieldSize || len > maxMessageLength then
        throw s!"invalid message length {len} (tag {tag})"
      else if hend : buffered.size < 1 + len then
        pure { buffered, messages }
      else
        let payload := buffered.extract (1 + lengthFieldSize) (1 + len)
        let rest := buffered.extract (1 + len) buffered.size
        parseBuffered rest (messages.push { tag, payload })
  termination_by buffered.size
  decreasing_by
    simp only [ByteArray.size_extract, lengthFieldSize] at *
    simp only [decide_eq_true_eq, Bool.or_eq_true, not_or] at hlen
    omega

def DecodeState.feed (state : DecodeState) (chunk : ByteArray) :
    Except String DecodeState :=
  parseBuffered (state.buffered ++ chunk) state.messages

/-- Drains completed messages, keeping any partial trailing bytes buffered. -/
def DecodeState.take (state : DecodeState) : Array RawMessage × DecodeState :=
  (state.messages, { state with messages := #[] })

/-- Backend message tags a client must recognize (protocol 3.0). -/
inductive BackendTag where
  | authentication          -- 'R'
  | backendKeyData          -- 'K'
  | bindComplete            -- '2'
  | closeComplete           -- '3'
  | commandComplete         -- 'C'
  | copyData                -- 'd'
  | copyDone                -- 'c'
  | copyInResponse          -- 'G'
  | copyOutResponse         -- 'H'
  | copyBothResponse        -- 'W'
  | dataRow                 -- 'D'
  | emptyQueryResponse      -- 'I'
  | errorResponse           -- 'E'
  | functionCallResponse    -- 'V'
  | negotiateProtocolVersion -- 'v'
  | noData                  -- 'n'
  | noticeResponse          -- 'N'
  | notificationResponse    -- 'A'
  | parameterDescription    -- 't'
  | parameterStatus         -- 'S'
  | parseComplete           -- '1'
  | portalSuspended         -- 's'
  | readyForQuery           -- 'Z'
  | rowDescription          -- 'T'
  | unknown (value : UInt8)
  deriving Inhabited, Repr, DecidableEq

namespace BackendTag

def ofUInt8 : UInt8 → BackendTag
  | 82 => .authentication
  | 75 => .backendKeyData
  | 50 => .bindComplete
  | 51 => .closeComplete
  | 67 => .commandComplete
  | 100 => .copyData
  | 99 => .copyDone
  | 71 => .copyInResponse
  | 72 => .copyOutResponse
  | 87 => .copyBothResponse
  | 68 => .dataRow
  | 73 => .emptyQueryResponse
  | 69 => .errorResponse
  | 86 => .functionCallResponse
  | 118 => .negotiateProtocolVersion
  | 110 => .noData
  | 78 => .noticeResponse
  | 65 => .notificationResponse
  | 116 => .parameterDescription
  | 83 => .parameterStatus
  | 49 => .parseComplete
  | 115 => .portalSuspended
  | 90 => .readyForQuery
  | 84 => .rowDescription
  | value => .unknown value

def toUInt8 : BackendTag → UInt8
  | .authentication => 82
  | .backendKeyData => 75
  | .bindComplete => 50
  | .closeComplete => 51
  | .commandComplete => 67
  | .copyData => 100
  | .copyDone => 99
  | .copyInResponse => 71
  | .copyOutResponse => 72
  | .copyBothResponse => 87
  | .dataRow => 68
  | .emptyQueryResponse => 73
  | .errorResponse => 69
  | .functionCallResponse => 86
  | .negotiateProtocolVersion => 118
  | .noData => 110
  | .noticeResponse => 78
  | .notificationResponse => 65
  | .parameterDescription => 116
  | .parameterStatus => 83
  | .parseComplete => 49
  | .portalSuspended => 115
  | .readyForQuery => 90
  | .rowDescription => 84
  | .unknown value => value

end BackendTag

/-- Frontend message tags (post-startup). -/
inductive FrontendTag where
  | bind          -- 'B'
  | close         -- 'C'
  | copyData      -- 'd'
  | copyDone      -- 'c'
  | copyFail      -- 'f'
  | describe      -- 'D'
  | execute       -- 'E'
  | flush         -- 'H'
  | functionCall  -- 'F'
  | parse         -- 'P'
  | password      -- 'p' (also SASL/GSS responses)
  | query         -- 'Q'
  | sync          -- 'S'
  | terminate     -- 'X'
  deriving Inhabited, Repr, DecidableEq

namespace FrontendTag

def toUInt8 : FrontendTag → UInt8
  | .bind => 66
  | .close => 67
  | .copyData => 100
  | .copyDone => 99
  | .copyFail => 102
  | .describe => 68
  | .execute => 69
  | .flush => 72
  | .functionCall => 70
  | .parse => 80
  | .password => 112
  | .query => 81
  | .sync => 83
  | .terminate => 88

end FrontendTag

/-- Convenience: frame a frontend message from its typed tag. -/
def frame (tag : FrontendTag) (payload : ByteArray := ByteArray.empty) : ByteArray :=
  RawMessage.encode { tag := tag.toUInt8, payload }

/-- The simple-query message: `Q` + SQL as cstring. -/
def encodeQuery (sql : String) : ByteArray :=
  frame .query (putCString ByteArray.empty sql)

def encodeTerminate : ByteArray :=
  frame .terminate

/-!
### Framing laws

Conservation: a successful `DecodeState.feed` step neither invents nor drops
bytes — re-encoding every accumulated message and appending the retained
buffer reproduces exactly the bytes fed so far. `RawMessage.encode` is
byte-exact for decoded frames because the decoder only accepts frames whose
length field equals `payload.size + lengthFieldSize`, which is precisely what
the encoder writes back.
-/

/-- Byte-exact re-encoder for a decoded message stream. -/
def encodeMessages (msgs : Array RawMessage) : ByteArray :=
  msgs.foldl (fun acc m => acc ++ m.encode) ByteArray.empty

theorem encodeMessages_push (msgs : Array RawMessage) (m : RawMessage) :
    encodeMessages (msgs.push m) = encodeMessages msgs ++ m.encode := by
  simp [encodeMessages]

theorem get!_eq_getElem {a : ByteArray} {i : Nat} (h : i < a.size) :
    a.get! i = a[i] := by
  rcases a with ⟨data⟩
  show data[i]! = _
  rw [getElem!_pos data i (by simpa using h)]
  simp [ByteArray.getElem_eq_getElem_data]

theorem getUInt32?_bound {bytes : ByteArray} {off : Nat} {v : UInt32}
    (h : getUInt32? bytes off = some v) : off + 4 ≤ bytes.size := by
  by_cases hle : off + 4 ≤ bytes.size
  · exact hle
  · simp [getUInt32?, hle] at h

private theorem getUInt32?_spec {bytes : ByteArray} {off : Nat} {v : UInt32}
    (h : getUInt32? bytes off = some v) (h4 : off + 4 ≤ bytes.size) :
    v = (bytes[off]'(by omega)).toUInt32 <<< 24 |||
        (bytes[off + 1]'(by omega)).toUInt32 <<< 16 |||
        (bytes[off + 2]'(by omega)).toUInt32 <<< 8 |||
        (bytes[off + 3]'(by omega)).toUInt32 := by
  simp only [getUInt32?, if_pos h4, Option.some.injEq] at h
  rw [← h,
    get!_eq_getElem (show off < bytes.size by omega),
    get!_eq_getElem (show off + 1 < bytes.size by omega),
    get!_eq_getElem (show off + 2 < bytes.size by omega),
    get!_eq_getElem (show off + 3 < bytes.size by omega)]

/-- Big-endian packing then unpacking each byte is the identity. -/
private theorem pack_unpack (b0 b1 b2 b3 : UInt8) :
    (((b0.toUInt32 <<< 24 ||| b1.toUInt32 <<< 16 ||| b2.toUInt32 <<< 8 |||
        b3.toUInt32) >>> 24).toUInt8 = b0) ∧
    (((b0.toUInt32 <<< 24 ||| b1.toUInt32 <<< 16 ||| b2.toUInt32 <<< 8 |||
        b3.toUInt32) >>> 16).toUInt8 = b1) ∧
    (((b0.toUInt32 <<< 24 ||| b1.toUInt32 <<< 16 ||| b2.toUInt32 <<< 8 |||
        b3.toUInt32) >>> 8).toUInt8 = b2) ∧
    ((b0.toUInt32 <<< 24 ||| b1.toUInt32 <<< 16 ||| b2.toUInt32 <<< 8 |||
        b3.toUInt32).toUInt8 = b3) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> bv_decide

private theorem putUInt32_empty (v : UInt32) :
    putUInt32 ByteArray.empty v =
      [(v >>> 24).toUInt8, (v >>> 16).toUInt8, (v >>> 8).toUInt8, v.toUInt8].toByteArray := by
  show ((((ByteArray.empty.push _).push _).push _).push _) = _
  simp only [← ByteArray.append_toByteArray_singleton, ← List.toByteArray_append,
    ByteArray.empty_append, List.cons_append, List.nil_append]

private theorem putUInt16_empty (v : UInt16) :
    putUInt16 ByteArray.empty v = [(v >>> 8).toUInt8, v.toUInt8].toByteArray := by
  show ((ByteArray.empty.push _).push _) = _
  simp only [← ByteArray.append_toByteArray_singleton, ← List.toByteArray_append,
    ByteArray.empty_append, List.cons_append, List.nil_append]

/-- The writers append: writing onto `a` is `a ++` writing onto empty. -/
theorem putUInt16_append (a : ByteArray) (v : UInt16) :
    putUInt16 a v = a ++ putUInt16 ByteArray.empty v := by
  show (a.push _).push _ = a ++ ((ByteArray.empty.push _).push _)
  simp only [← ByteArray.append_toByteArray_singleton, ByteArray.append_assoc,
    ByteArray.empty_append]

theorem putUInt32_append (a : ByteArray) (v : UInt32) :
    putUInt32 a v = a ++ putUInt32 ByteArray.empty v := by
  show (((a.push _).push _).push _).push _ =
    a ++ ((((ByteArray.empty.push _).push _).push _).push _)
  simp only [← ByteArray.append_toByteArray_singleton, ByteArray.append_assoc,
    ByteArray.empty_append]

theorem size_putUInt16 (a : ByteArray) (v : UInt16) :
    (putUInt16 a v).size = a.size + 2 := by
  show ((a.push _).push _).size = a.size + 2
  simp only [ByteArray.size_push]

theorem size_putUInt32 (a : ByteArray) (v : UInt32) :
    (putUInt32 a v).size = a.size + 4 := by
  show ((((a.push _).push _).push _).push _).size = a.size + 4
  simp only [ByteArray.size_push]

/-- Big-endian 16-bit write/read roundtrip. -/
theorem getUInt16?_putUInt16 (v : UInt16) :
    getUInt16? (putUInt16 ByteArray.empty v) 0 = some v := by
  rw [putUInt16_empty]
  have hsz : ([(v >>> 8).toUInt8, v.toUInt8].toByteArray).size = 2 :=
    List.size_toByteArray
  rw [getUInt16?, if_pos (by omega)]
  rw [get!_eq_getElem (by omega), get!_eq_getElem (by omega)]
  simp only [List.getElem_toByteArray, List.getElem_cons_zero, List.getElem_cons_succ]
  congr 1
  bv_decide

theorem putInt32_eq (a : ByteArray) (v : Int32) :
    putInt32 a v = putUInt32 a v.toUInt32 := by rfl

theorem size_putInt32 (a : ByteArray) (v : Int32) :
    (putInt32 a v).size = a.size + 4 := by
  rw [putInt32_eq]
  exact size_putUInt32 a v.toUInt32

/-- Big-endian 32-bit write/read roundtrip. -/
theorem getUInt32?_putUInt32 (v : UInt32) :
    getUInt32? (putUInt32 ByteArray.empty v) 0 = some v := by
  rw [putUInt32_empty]
  have hsz : ([(v >>> 24).toUInt8, (v >>> 16).toUInt8, (v >>> 8).toUInt8,
      v.toUInt8].toByteArray).size = 4 :=
    List.size_toByteArray
  rw [getUInt32?, if_pos (by omega)]
  rw [get!_eq_getElem (by omega), get!_eq_getElem (by omega),
    get!_eq_getElem (by omega), get!_eq_getElem (by omega)]
  simp only [List.getElem_toByteArray, List.getElem_cons_zero, List.getElem_cons_succ]
  congr 1
  bv_decide

/-- A decoded frame re-encodes to exactly the bytes it was cut from. -/
private theorem encode_extract {buffered : ByteArray} {len32 : UInt32}
    (hget : getUInt32? buffered 1 = some len32)
    (hlen : lengthFieldSize ≤ len32.toNat)
    (hsize : 1 + len32.toNat ≤ buffered.size) :
    RawMessage.encode
        { tag := buffered.get! 0
          payload := buffered.extract (1 + lengthFieldSize) (1 + len32.toNat) } =
      buffered.extract 0 (1 + len32.toNat) := by
  have h5 : 1 + 4 ≤ buffered.size := getUInt32?_bound hget
  simp only [lengthFieldSize] at hlen ⊢
  have hpay : (buffered.extract (1 + 4) (1 + len32.toNat)).size = len32.toNat - 4 := by
    simp only [ByteArray.size_extract]; omega
  have hv : ((buffered.extract (1 + 4) (1 + len32.toNat)).size + 4).toUInt32 = len32 := by
    rw [hpay]
    have : len32.toNat - 4 + 4 = len32.toNat := by omega
    rw [this]
    exact UInt32.ofNat_toNat
  rw [RawMessage.encode]
  simp only [lengthFieldSize, hv]
  have hspec := getUInt32?_spec hget (by omega)
  obtain ⟨e0, e1, e2, e3⟩ := pack_unpack (buffered[1]'(by omega))
    (buffered[1 + 1]'(by omega)) (buffered[1 + 2]'(by omega)) (buffered[1 + 3]'(by omega))
  rw [ByteArray.extract_eq_extract_append_extract (a := buffered) (i := 0)
      (k := 1 + len32.toNat) 1 (by omega) (by omega),
    ByteArray.extract_eq_extract_append_extract (a := buffered) (i := 1)
      (k := 1 + len32.toNat) (1 + 4) (by omega) (by omega)]
  have hhead : (ByteArray.empty.push (buffered.get! 0)) = buffered.extract 0 1 := by
    rw [ByteArray.extract_add_one (i := 0) (by omega)]
    rw [get!_eq_getElem (show 0 < buffered.size by omega)]
    rw [← ByteArray.append_toByteArray_singleton, ByteArray.empty_append]
    rfl
  have hlenbytes : putUInt32 ByteArray.empty len32 = buffered.extract 1 (1 + 4) := by
    rw [putUInt32_empty, ByteArray.extract_add_four (by omega), hspec, e0, e1, e2, e3]
    rfl
  calc putUInt32 (ByteArray.empty.push (buffered.get! 0)) len32 ++
          buffered.extract (1 + 4) (1 + len32.toNat)
      = (ByteArray.empty.push (buffered.get! 0) ++ putUInt32 ByteArray.empty len32) ++
          buffered.extract (1 + 4) (1 + len32.toNat) := by
        rw [putUInt32, putUInt32]
        simp only [← ByteArray.append_toByteArray_singleton, ByteArray.append_assoc,
          ByteArray.empty_append]
    _ = buffered.extract 0 1 ++ (buffered.extract 1 (1 + 4) ++
          buffered.extract (1 + 4) (1 + len32.toNat)) := by
        rw [hhead, hlenbytes, ByteArray.append_assoc]

/-- Parsing never invents or drops bytes: re-encoding all accumulated messages
and appending the retained buffer is a left-invariant of the scan. -/
private theorem parseBuffered_conservation {buffered : ByteArray}
    {messages : Array RawMessage} :
    ∀ {st : DecodeState}, parseBuffered buffered messages = .ok st →
      encodeMessages st.messages ++ st.buffered = encodeMessages messages ++ buffered := by
  fun_induction parseBuffered buffered messages with
  | case1 buffered messages _ =>
    intro st h
    cases h
    rfl
  | case2 buffered messages _ _ =>
    intro st h
    cases h
    rfl
  | case3 =>
    intro st h
    cases h
  | case4 =>
    intro st h
    cases h
    rfl
  | case5 =>
    rename_i buffered messages hsize len32 hget tag len hlen hend payload rest ih
    intro st h
    have hstep := ih h
    rw [encodeMessages_push] at hstep
    rw [hstep, ByteArray.append_assoc]
    congr 1
    have hlenEq : len = len32.toNat := rfl
    simp only [decide_eq_true_eq, Bool.or_eq_true, not_or] at hlen
    have hlen4 : lengthFieldSize ≤ len32.toNat := by
      rw [← hlenEq]; exact Nat.le_of_not_lt hlen.1
    show RawMessage.encode
        { tag := buffered.get! 0
          payload := buffered.extract (1 + lengthFieldSize) (1 + len32.toNat) } ++
        buffered.extract (1 + len32.toNat) buffered.size = buffered
    rw [encode_extract hget hlen4 (by omega)]
    rw [← ByteArray.extract_eq_extract_append_extract (a := buffered) (i := 0)
      (k := buffered.size) (1 + len32.toNat) (by omega) (by omega)]
    exact ByteArray.extract_zero_size

/-- Conservation for the shell entry point: one successful `feed` preserves
the byte stream exactly — re-encoded messages plus the retained buffer equal
the previously retained buffer plus the fed chunk. -/
theorem DecodeState.feed_conservation {s : DecodeState} {chunk : ByteArray}
    {s' : DecodeState} (h : s.feed chunk = .ok s') :
    encodeMessages s'.messages ++ s'.buffered =
      encodeMessages s.messages ++ (s.buffered ++ chunk) := by
  have := parseBuffered_conservation (buffered := s.buffered ++ chunk)
    (messages := s.messages) h
  exact this

/-- Conservation in drained form (`messages` empty, e.g. right after `take`):
the emitted messages plus the retained buffer are exactly the input bytes. -/
theorem DecodeState.feed_conservation_drained {s : DecodeState} {chunk : ByteArray}
    {s' : DecodeState} (hm : s.messages = #[]) (h : s.feed chunk = .ok s') :
    encodeMessages s'.messages ++ s'.buffered = s.buffered ++ chunk := by
  have := DecodeState.feed_conservation h
  rwa [hm, show encodeMessages #[] = ByteArray.empty from rfl,
    ByteArray.empty_append] at this

/-!
### Partition invariance

Chunk boundaries are invisible: feeding one big chunk equals feeding any
split of it (`feed_append`), so any two chunkings of the same byte stream
produce the same messages, residual buffer, and error behavior
(`feed_partition_invariant`).
-/

private theorem get!_append_left {a b : ByteArray} {i : Nat} (h : i < a.size) :
    (a ++ b).get! i = a.get! i := by
  rw [get!_eq_getElem (show i < (a ++ b).size by rw [ByteArray.size_append]; omega),
    get!_eq_getElem h]
  exact ByteArray.getElem_append_left h

theorem getUInt32?_append_left {a b : ByteArray} {off : Nat}
    (h : off + 4 ≤ a.size) :
    getUInt32? (a ++ b) off = getUInt32? a off := by
  unfold getUInt32?
  rw [if_pos h, if_pos (show off + 4 ≤ (a ++ b).size by rw [ByteArray.size_append]; omega)]
  rw [get!_append_left (by omega), get!_append_left (by omega),
    get!_append_left (by omega), get!_append_left (by omega)]

private theorem get!_append_right {a b : ByteArray} {i : Nat}
    (h : a.size ≤ i) (h2 : i < a.size + b.size) :
    (a ++ b).get! i = b.get! (i - a.size) := by
  rw [get!_eq_getElem (show i < (a ++ b).size by rw [ByteArray.size_append]; omega),
    get!_eq_getElem (by omega)]
  exact ByteArray.getElem_append_right h

/-- Reading past a prefix reads the suffix. -/
theorem getUInt32?_append_right {a b : ByteArray} {off : Nat} (h : a.size ≤ off) :
    getUInt32? (a ++ b) off = getUInt32? b (off - a.size) := by
  unfold getUInt32?
  rw [ByteArray.size_append]
  by_cases hle : off - a.size + 4 ≤ b.size
  · rw [if_pos (by omega), if_pos hle]
    rw [get!_append_right (by omega) (by omega), get!_append_right (by omega) (by omega),
      get!_append_right (by omega) (by omega), get!_append_right (by omega) (by omega)]
    have e1 : off + 1 - a.size = off - a.size + 1 := by omega
    have e2 : off + 2 - a.size = off - a.size + 2 := by omega
    have e3 : off + 3 - a.size = off - a.size + 3 := by omega
    rw [e1, e2, e3]
  · rw [if_neg (by omega), if_neg hle]

private theorem extract_append_left_of_le {a b : ByteArray} {i j : Nat}
    (hij : i ≤ j) (hj : j ≤ a.size) : (a ++ b).extract i j = a.extract i j := by
  rw [ByteArray.extract_append,
    Nat.sub_eq_zero_of_le (Nat.le_trans hij hj),
    Nat.sub_eq_zero_of_le hj,
    ByteArray.extract_same, ByteArray.append_empty]

private theorem extract_append_chunk {a b : ByteArray} {i : Nat} (hi : i ≤ a.size) :
    (a ++ b).extract i (a ++ b).size = a.extract i a.size ++ b := by
  rw [ByteArray.size_append, ByteArray.extract_append,
    Nat.sub_eq_zero_of_le hi, Nat.add_sub_cancel_left, ByteArray.extract_zero_size]
  congr 1
  apply ByteArray.ext_getElem
  · simp only [ByteArray.size_extract]
    omega
  · intro k hk hk'
    rw [ByteArray.getElem_extract, ByteArray.getElem_extract]

/-- One scan step commutes with appending more bytes: parsing `buffered ++ b`
is parsing `buffered` first, then continuing on the retained residue plus
`b` — including identical error behavior. -/
private theorem parseBuffered_append (buffered : ByteArray)
    (messages : Array RawMessage) (b : ByteArray) :
    parseBuffered (buffered ++ b) messages =
      (parseBuffered buffered messages).bind
        (fun st => parseBuffered (st.buffered ++ b) st.messages) := by
  fun_induction parseBuffered buffered messages with
  | case1 buffered messages hsize =>
    rfl
  | case2 buffered messages hsize hget =>
    rw [getUInt32?, if_pos (by simp only [lengthFieldSize] at hsize; omega)] at hget
    cases hget
  | case3 =>
    rename_i buffered messages hsize len32 hget tag len hlen
    have hsize5 : 1 + 4 ≤ buffered.size := by
      simp only [lengthFieldSize] at hsize; omega
    have hlen' : (decide (len32.toNat < lengthFieldSize) ||
        decide (len32.toNat > maxMessageLength)) = true := hlen
    rw [parseBuffered.eq_def]
    rw [if_neg (show ¬(buffered ++ b).size < 1 + lengthFieldSize by
      rw [ByteArray.size_append]; omega)]
    rw [getUInt32?_append_left (by omega)]
    simp only [hget]
    rw [dif_pos hlen']
    rw [get!_append_left (show 0 < buffered.size by omega)]
    rfl
  | case4 =>
    rename_i buffered messages hsize len32 hget len hlen hend
    rfl
  | case5 =>
    rename_i buffered messages hsize len32 hget tag len hlen hend payload rest ih
    have hsize5 : 1 + 4 ≤ buffered.size := by
      simp only [lengthFieldSize] at hsize; omega
    have hlen4 : lengthFieldSize ≤ len := by
      simp only [decide_eq_true_eq, Bool.or_eq_true, not_or] at hlen
      exact Nat.le_of_not_lt hlen.1
    simp only [lengthFieldSize] at hlen4
    have hlenEq : len = len32.toNat := rfl
    have hlen' : ¬(decide (len32.toNat < lengthFieldSize) ||
        decide (len32.toNat > maxMessageLength)) = true := hlen
    have hend' : 1 + len32.toNat ≤ buffered.size := by omega
    rw [parseBuffered.eq_def]
    rw [if_neg (show ¬(buffered ++ b).size < 1 + lengthFieldSize by
      rw [ByteArray.size_append]; omega)]
    rw [getUInt32?_append_left (by omega)]
    simp only [hget]
    rw [dif_neg hlen']
    rw [dif_neg (show ¬(buffered ++ b).size < 1 + len32.toNat by
      rw [ByteArray.size_append]; omega)]
    rw [get!_append_left (show 0 < buffered.size by omega)]
    rw [extract_append_left_of_le (a := buffered) (b := b) (i := 1 + lengthFieldSize)
      (j := 1 + len32.toNat) (by simp only [lengthFieldSize]; omega) (by omega)]
    rw [extract_append_chunk (a := buffered) (b := b) (i := 1 + len32.toNat) (by omega)]
    exact ih

/-- Feeding a concatenation is feeding its parts in sequence. -/
theorem DecodeState.feed_append (s : DecodeState) (a b : ByteArray) :
    s.feed (a ++ b) = (s.feed a).bind (fun st => st.feed b) := by
  show parseBuffered (s.buffered ++ (a ++ b)) s.messages = _
  rw [← ByteArray.append_assoc, parseBuffered_append]
  rfl

/-- Feeding chunks one at a time equals feeding their concatenation. -/
theorem DecodeState.feed_chunks (s : DecodeState) (c : ByteArray)
    (cs : List ByteArray) :
    List.foldlM DecodeState.feed s (c :: cs) = s.feed (cs.foldl (· ++ ·) c) := by
  induction cs generalizing s c with
  | nil => simp [List.foldlM_cons, List.foldlM_nil, List.foldl_nil]
  | cons d ds ih =>
    have hassoc : ∀ (x y : ByteArray) (l : List ByteArray),
        l.foldl (· ++ ·) (x ++ y) = x ++ l.foldl (· ++ ·) y := by
      intro x y l
      induction l generalizing y with
      | nil => rfl
      | cons z zs ihz =>
        rw [List.foldl_cons, List.foldl_cons, ByteArray.append_assoc, ihz]
    rw [List.foldlM_cons]
    calc (s.feed c).bind (fun st => List.foldlM DecodeState.feed st (d :: ds))
        = (s.feed c).bind (fun st => st.feed (ds.foldl (· ++ ·) d)) := by
          cases s.feed c with
          | error e => rfl
          | ok st => simp only [Except.bind]; exact ih st d
      _ = s.feed (c ++ ds.foldl (· ++ ·) d) := (s.feed_append c _).symm
      _ = s.feed (List.foldl (· ++ ·) (c ++ d) ds) := by rw [hassoc]
      _ = s.feed ((d :: ds).foldl (· ++ ·) c) := by rw [List.foldl_cons]

/-- **Partition invariance**: any two chunkings of the same byte stream give
the same parse — same messages, same residual buffer, same errors. -/
theorem DecodeState.feed_partition_invariant (s : DecodeState)
    {c d : ByteArray} {cs ds : List ByteArray}
    (h : cs.foldl (· ++ ·) c = ds.foldl (· ++ ·) d) :
    List.foldlM DecodeState.feed s (c :: cs) =
      List.foldlM DecodeState.feed s (d :: ds) := by
  rw [DecodeState.feed_chunks, DecodeState.feed_chunks, h]

end Protocol
end Pg
