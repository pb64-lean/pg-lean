module

public import Pg.Crypto.Sha256

public section

namespace Pg
namespace Crypto

/-!
HMAC-SHA-256 (RFC 2104 / FIPS 198-1). Only the SHA-256 instantiation is
provided; it is all SCRAM-SHA-256 needs.
-/

private def xorPad (key : ByteArray) (pad : UInt8) : ByteArray := Id.run do
  let mut out := ByteArray.empty
  for i in [0:key.size] do
    out := out.push (key.get! i ^^^ pad)
  return out

def hmacSha256 (key msg : ByteArray) : ByteArray :=
  let key := if key.size > 64 then sha256 key else key
  let key := Id.run do
    let mut k := key
    for _ in [0:64 - key.size] do
      k := k.push 0
    return k
  sha256 (xorPad key 0x5c ++ sha256 (xorPad key 0x36 ++ msg))

end Crypto
end Pg
