/-!
# RFC 4648 §4 — Base 64 Encoding

Encoder and strict decoder for base64.

The core functions `encodeList` and `decodeList` operate on `List UInt8` /
`List Char` by structural recursion over 3-byte / 4-character groups, which
keeps them easy to reason about in proofs. `encode` and `decode?` are the
user-facing wrappers over `ByteArray` and `String`.

The decoder is strict in the sense of RFC 4648 §3.5 and §12: it rejects
characters outside the alphabet, misplaced or missing padding, and non-zero
pad bits. Consequently `decode?` accepts exactly the outputs of `encode`.
-/

namespace Rfc4648.Base64

/-- Map a 6-bit value (`0`–`63`) to its character in the base64 alphabet
(RFC 4648 Table 1): `A`–`Z`, `a`–`z`, `0`–`9`, `+`, `/`. -/
def toChar (v : UInt8) : Char :=
  if v < 26 then Char.ofNat ('A'.toNat + v.toNat)
  else if v < 52 then Char.ofNat ('a'.toNat + (v.toNat - 26))
  else if v < 62 then Char.ofNat ('0'.toNat + (v.toNat - 52))
  else if v = 62 then '+'
  else '/'

/-- Map a character to its 6-bit value, or `none` if it is not in the
base64 alphabet. Inverse of `toChar`. -/
def ofChar? (c : Char) : Option UInt8 :=
  if 'A' ≤ c ∧ c ≤ 'Z' then some (c.toNat.toUInt8 - 'A'.toNat.toUInt8)
  else if 'a' ≤ c ∧ c ≤ 'z' then some (c.toNat.toUInt8 - 'a'.toNat.toUInt8 + 26)
  else if '0' ≤ c ∧ c ≤ '9' then some (c.toNat.toUInt8 - '0'.toNat.toUInt8 + 52)
  else if c = '+' then some 62
  else if c = '/' then some 63
  else none

/-- Encode bytes as base64 characters, processing one 24-bit group
(3 bytes → 4 characters) per step. A final group of 1 or 2 bytes is
zero-padded to a whole number of 6-bit values and the output filled to
4 characters with `=` (RFC 4648 §4). -/
def encodeList : List UInt8 → List Char
  | [] => []
  | [b0] =>
    [toChar (b0 >>> 2),
     toChar ((b0 &&& 0x03) <<< 4),
     '=', '=']
  | [b0, b1] =>
    [toChar (b0 >>> 2),
     toChar (((b0 &&& 0x03) <<< 4) ||| (b1 >>> 4)),
     toChar ((b1 &&& 0x0F) <<< 2),
     '=']
  | b0 :: b1 :: b2 :: rest =>
    toChar (b0 >>> 2) ::
    toChar (((b0 &&& 0x03) <<< 4) ||| (b1 >>> 4)) ::
    toChar (((b1 &&& 0x0F) <<< 2) ||| (b2 >>> 6)) ::
    toChar (b2 &&& 0x3F) ::
    encodeList rest

/-- Strictly decode base64 characters, one 4-character group per step.
Returns `none` unless the input is a canonical encoding: length a multiple
of 4, padding only in the final group, and all pad bits zero. -/
def decodeList : List Char → Option (List UInt8)
  | [] => some []
  | c0 :: c1 :: c2 :: c3 :: rest => do
    let v0 ← ofChar? c0
    let v1 ← ofChar? c1
    if c2 = '=' then
      -- "xx==": one output byte; the low 4 bits of v1 are pad bits.
      if c3 = '=' ∧ rest = [] ∧ v1 &&& 0x0F = 0 then
        some [(v0 <<< 2) ||| (v1 >>> 4)]
      else none
    else do
      let v2 ← ofChar? c2
      if c3 = '=' then
        -- "xxx=": two output bytes; the low 2 bits of v2 are pad bits.
        if rest = [] ∧ v2 &&& 0x03 = 0 then
          some [(v0 <<< 2) ||| (v1 >>> 4),
                (v1 <<< 4) ||| (v2 >>> 2)]
        else none
      else do
        let v3 ← ofChar? c3
        let tail ← decodeList rest
        some (((v0 <<< 2) ||| (v1 >>> 4)) ::
              ((v1 <<< 4) ||| (v2 >>> 2)) ::
              ((v2 <<< 6) ||| v3) ::
              tail)
  | _ => none

/-- Encode a byte array as a base64 string (RFC 4648 §4, with padding). -/
def encode (data : ByteArray) : String :=
  String.ofList (encodeList data.toList)

/-- Strictly decode a base64 string. Returns `none` if the input is not a
canonical RFC 4648 §4 encoding. -/
def decode? (s : String) : Option ByteArray :=
  (decodeList s.toList).map fun bytes => ByteArray.mk bytes.toArray

/-! ## Test vectors (RFC 4648 §10), checked at compile time -/

#guard encode "".toUTF8 = ""
#guard encode "f".toUTF8 = "Zg=="
#guard encode "fo".toUTF8 = "Zm8="
#guard encode "foo".toUTF8 = "Zm9v"
#guard encode "foob".toUTF8 = "Zm9vYg=="
#guard encode "fooba".toUTF8 = "Zm9vYmE="
#guard encode "foobar".toUTF8 = "Zm9vYmFy"

#guard (decode? "").map ByteArray.toList = some "".toUTF8.toList
#guard (decode? "Zg==").map ByteArray.toList = some "f".toUTF8.toList
#guard (decode? "Zm8=").map ByteArray.toList = some "fo".toUTF8.toList
#guard (decode? "Zm9v").map ByteArray.toList = some "foo".toUTF8.toList
#guard (decode? "Zm9vYg==").map ByteArray.toList = some "foob".toUTF8.toList
#guard (decode? "Zm9vYmE=").map ByteArray.toList = some "fooba".toUTF8.toList
#guard (decode? "Zm9vYmFy").map ByteArray.toList = some "foobar".toUTF8.toList

/-! Strictness: malformed inputs are rejected. -/

#guard (decode? "Zm9").isNone          -- length not a multiple of 4
#guard (decode? "Zm9v!A==").isNone     -- character outside the alphabet
#guard (decode? "Zh==").isNone         -- non-zero pad bits ("Zg==" is canonical)
#guard (decode? "Zm9=").isNone         -- non-zero pad bits ("Zm8=" is canonical)
#guard (decode? "Zg==Zg==").isNone     -- padding before the final group
#guard (decode? "Zg=a").isNone         -- '=' not at the end of the group
#guard (decode? "====").isNone         -- padding alone is not a group

end Rfc4648.Base64
