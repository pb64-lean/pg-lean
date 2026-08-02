module

public import Pg.Crypto.Hmac

public section

namespace Pg
namespace Crypto

/-!
PBKDF2-HMAC-SHA-256 (RFC 8018). SCRAM's `Hi(str, salt, i)` is exactly
PBKDF2-HMAC-SHA-256 with dkLen = 32 (one block); the general multi-block
form is implemented anyway since it is the natural unit to test and reuse.
-/

private def xorBytes (a b : ByteArray) : ByteArray := Id.run do
  let mut out := ByteArray.empty
  for i in [0:a.size] do
    out := out.push (a.get! i ^^^ b.get! i)
  return out

/-- One PBKDF2 block: `F(P, S, c, i) = U_1 ^ U_2 ^ ... ^ U_c`. -/
private def block (password salt : ByteArray) (iterations blockIndex : Nat) : ByteArray := Id.run do
  let idx : UInt32 := UInt32.ofNat blockIndex
  let seed := salt
    |>.push (idx >>> 24).toUInt8
    |>.push (idx >>> 16).toUInt8
    |>.push (idx >>> 8).toUInt8
    |>.push idx.toUInt8
  let mut u := hmacSha256 password seed
  let mut acc := u
  for _ in [0:iterations - 1] do
    u := hmacSha256 password u
    acc := xorBytes acc u
  return acc

def pbkdf2HmacSha256 (password salt : ByteArray) (iterations : Nat) (dkLen : Nat := 32) :
    ByteArray := Id.run do
  if iterations == 0 then
    return ByteArray.empty
  let mut out := ByteArray.empty
  let blocks := (dkLen + 31) / 32
  for i in [0:blocks] do
    out := out ++ block password salt iterations (i + 1)
  return out.extract 0 dkLen

end Crypto
end Pg
