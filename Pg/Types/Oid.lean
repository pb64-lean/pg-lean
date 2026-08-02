module

public section

namespace Pg
namespace Oid

/-! Stable core type OIDs (pg_type.dat; unchanged since time immemorial). -/

def bool : UInt32 := 16
def bytea : UInt32 := 17
def char : UInt32 := 18
def name : UInt32 := 19
def int8 : UInt32 := 20
def int2 : UInt32 := 21
def int4 : UInt32 := 23
def text : UInt32 := 25
def oid : UInt32 := 26
def json : UInt32 := 114
def float4 : UInt32 := 700
def float8 : UInt32 := 701
def bpchar : UInt32 := 1042
def varchar : UInt32 := 1043
def date : UInt32 := 1082
def time : UInt32 := 1083
def timestamp : UInt32 := 1114
def timestamptz : UInt32 := 1184
def interval : UInt32 := 1186
def numeric : UInt32 := 1700
def uuid : UInt32 := 2950
def jsonb : UInt32 := 3802

def boolArray : UInt32 := 1000
def byteaArray : UInt32 := 1001
def int2Array : UInt32 := 1005
def int4Array : UInt32 := 1007
def textArray : UInt32 := 1009
def varcharArray : UInt32 := 1015
def int8Array : UInt32 := 1016
def float4Array : UInt32 := 1021
def float8Array : UInt32 := 1022
def numericArray : UInt32 := 1231
def timestampArray : UInt32 := 1115
def timestamptzArray : UInt32 := 1185
def dateArray : UInt32 := 1182
def uuidArray : UInt32 := 2951

/-- Element OID for a known array OID (0 = unknown). -/
def arrayElem : UInt32 → UInt32
  | 1000 => bool
  | 1001 => bytea
  | 1005 => int2
  | 1007 => int4
  | 1009 => text
  | 1015 => varchar
  | 1016 => int8
  | 1021 => float4
  | 1022 => float8
  | 1231 => numeric
  | 1115 => timestamp
  | 1185 => timestamptz
  | 1182 => date
  | 2951 => uuid
  | _ => 0

end Oid
end Pg
