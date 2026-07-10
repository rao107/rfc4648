/-!
# RFC 4648 §6 — Base 32 Encoding

Encoder and strict decoder for base32.

Base32 processes 40-bit groups: 5 bytes become 8 characters of 5 bits
each. A final group of 1, 2, 3, or 4 bytes is zero-padded to a whole
number of 5-bit values and the output filled to 8 characters with
6, 4, 3, or 1 `=` respectively.

As in `Rfc4648.Base64`, the core functions recurse structurally over
groups, and the decoder is strict (RFC 4648 §3.5, §12): it accepts
exactly the outputs of the encoder.
-/

namespace Rfc4648.Base32

/-- Map a 5-bit value (`0`–`31`) to its character in the base32 alphabet
(RFC 4648 Table 3): `A`–`Z`, `2`–`7`. -/
def toChar (v : UInt8) : Char :=
  if v < 26 then Char.ofNat ('A'.toNat + v.toNat)
  else Char.ofNat ('2'.toNat + (v.toNat - 26))

/-- Map a character to its 5-bit value, or `none` if it is not in the
base32 alphabet. Inverse of `toChar`. -/
def ofChar? (c : Char) : Option UInt8 :=
  if 'A' ≤ c ∧ c ≤ 'Z' then some (c.toNat.toUInt8 - 'A'.toNat.toUInt8)
  else if '2' ≤ c ∧ c ≤ '7' then some (c.toNat.toUInt8 - '2'.toNat.toUInt8 + 26)
  else none

/-- Encode bytes as base32 characters, processing one 40-bit group
(5 bytes → 8 characters) per step. A final group of 1–4 bytes is
zero-padded to a whole number of 5-bit values and the output filled to
8 characters with `=` (RFC 4648 §6). -/
def encodeList : List UInt8 → List Char
  | [] => []
  | [b0] =>
    [toChar (b0 >>> 3),
     toChar ((b0 &&& 0x07) <<< 2),
     '=', '=', '=', '=', '=', '=']
  | [b0, b1] =>
    [toChar (b0 >>> 3),
     toChar (((b0 &&& 0x07) <<< 2) ||| (b1 >>> 6)),
     toChar ((b1 >>> 1) &&& 0x1F),
     toChar ((b1 &&& 0x01) <<< 4),
     '=', '=', '=', '=']
  | [b0, b1, b2] =>
    [toChar (b0 >>> 3),
     toChar (((b0 &&& 0x07) <<< 2) ||| (b1 >>> 6)),
     toChar ((b1 >>> 1) &&& 0x1F),
     toChar (((b1 &&& 0x01) <<< 4) ||| (b2 >>> 4)),
     toChar ((b2 &&& 0x0F) <<< 1),
     '=', '=', '=']
  | [b0, b1, b2, b3] =>
    [toChar (b0 >>> 3),
     toChar (((b0 &&& 0x07) <<< 2) ||| (b1 >>> 6)),
     toChar ((b1 >>> 1) &&& 0x1F),
     toChar (((b1 &&& 0x01) <<< 4) ||| (b2 >>> 4)),
     toChar (((b2 &&& 0x0F) <<< 1) ||| (b3 >>> 7)),
     toChar ((b3 >>> 2) &&& 0x1F),
     toChar ((b3 &&& 0x03) <<< 3),
     '=']
  | b0 :: b1 :: b2 :: b3 :: b4 :: rest =>
    toChar (b0 >>> 3) ::
    toChar (((b0 &&& 0x07) <<< 2) ||| (b1 >>> 6)) ::
    toChar ((b1 >>> 1) &&& 0x1F) ::
    toChar (((b1 &&& 0x01) <<< 4) ||| (b2 >>> 4)) ::
    toChar (((b2 &&& 0x0F) <<< 1) ||| (b3 >>> 7)) ::
    toChar ((b3 >>> 2) &&& 0x1F) ::
    toChar (((b3 &&& 0x03) <<< 3) ||| (b4 >>> 5)) ::
    toChar (b4 &&& 0x1F) ::
    encodeList rest

/-- Strictly decode base32 characters, one 8-character group per step.
Returns `none` unless the input is a canonical encoding: length a multiple
of 8, padding (of a valid length: 1, 3, 4, or 6) only in the final group,
and all pad bits zero. -/
def decodeList : List Char → Option (List UInt8)
  | [] => some []
  | c0 :: c1 :: c2 :: c3 :: c4 :: c5 :: c6 :: c7 :: rest => do
    let v0 ← ofChar? c0
    let v1 ← ofChar? c1
    if c2 = '=' then
      -- "xx======": one output byte; the low 2 bits of v1 are pad bits.
      if c3 = '=' ∧ c4 = '=' ∧ c5 = '=' ∧ c6 = '=' ∧ c7 = '=' ∧ rest = [] ∧
          v1 &&& 0x03 = 0 then
        some [(v0 <<< 3) ||| (v1 >>> 2)]
      else none
    else do
      let v2 ← ofChar? c2
      let v3 ← ofChar? c3
      if c4 = '=' then
        -- "xxxx====": two output bytes; the low 4 bits of v3 are pad bits.
        if c5 = '=' ∧ c6 = '=' ∧ c7 = '=' ∧ rest = [] ∧ v3 &&& 0x0F = 0 then
          some [(v0 <<< 3) ||| (v1 >>> 2),
                (v1 <<< 6) ||| (v2 <<< 1) ||| (v3 >>> 4)]
        else none
      else do
        let v4 ← ofChar? c4
        if c5 = '=' then
          -- "xxxxx===": three output bytes; the low bit of v4 is a pad bit.
          if c6 = '=' ∧ c7 = '=' ∧ rest = [] ∧ v4 &&& 0x01 = 0 then
            some [(v0 <<< 3) ||| (v1 >>> 2),
                  (v1 <<< 6) ||| (v2 <<< 1) ||| (v3 >>> 4),
                  (v3 <<< 4) ||| (v4 >>> 1)]
          else none
        else do
          let v5 ← ofChar? c5
          let v6 ← ofChar? c6
          if c7 = '=' then
            -- "xxxxxxx=": four output bytes; the low 3 bits of v6 are pad bits.
            if rest = [] ∧ v6 &&& 0x07 = 0 then
              some [(v0 <<< 3) ||| (v1 >>> 2),
                    (v1 <<< 6) ||| (v2 <<< 1) ||| (v3 >>> 4),
                    (v3 <<< 4) ||| (v4 >>> 1),
                    (v4 <<< 7) ||| (v5 <<< 2) ||| (v6 >>> 3)]
            else none
          else do
            let v7 ← ofChar? c7
            let tail ← decodeList rest
            some (((v0 <<< 3) ||| (v1 >>> 2)) ::
                  ((v1 <<< 6) ||| (v2 <<< 1) ||| (v3 >>> 4)) ::
                  ((v3 <<< 4) ||| (v4 >>> 1)) ::
                  ((v4 <<< 7) ||| (v5 <<< 2) ||| (v6 >>> 3)) ::
                  ((v6 <<< 5) ||| v7) ::
                  tail)
  | _ => none

/-- Encode a byte array as a base32 string (RFC 4648 §6, with padding). -/
def encode (data : ByteArray) : String :=
  String.ofList (encodeList data.toList)

/-- Strictly decode a base32 string. Returns `none` if the input is not a
canonical RFC 4648 §6 encoding. -/
def decode? (s : String) : Option ByteArray :=
  (decodeList s.toList).map fun bytes => ByteArray.mk bytes.toArray

/-! ## Test vectors (RFC 4648 §10), checked at compile time -/

#guard encode "".toUTF8 = ""
#guard encode "f".toUTF8 = "MY======"
#guard encode "fo".toUTF8 = "MZXQ===="
#guard encode "foo".toUTF8 = "MZXW6==="
#guard encode "foob".toUTF8 = "MZXW6YQ="
#guard encode "fooba".toUTF8 = "MZXW6YTB"
#guard encode "foobar".toUTF8 = "MZXW6YTBOI======"

#guard (decode? "").map ByteArray.toList = some "".toUTF8.toList
#guard (decode? "MY======").map ByteArray.toList = some "f".toUTF8.toList
#guard (decode? "MZXQ====").map ByteArray.toList = some "fo".toUTF8.toList
#guard (decode? "MZXW6===").map ByteArray.toList = some "foo".toUTF8.toList
#guard (decode? "MZXW6YQ=").map ByteArray.toList = some "foob".toUTF8.toList
#guard (decode? "MZXW6YTB").map ByteArray.toList = some "fooba".toUTF8.toList
#guard (decode? "MZXW6YTBOI======").map ByteArray.toList = some "foobar".toUTF8.toList

/-! Strictness: malformed inputs are rejected. -/

#guard (decode? "MY=====").isNone           -- length not a multiple of 8
#guard (decode? "my======").isNone          -- lowercase is not canonical
#guard (decode? "M1======").isNone          -- '0', '1', '8', '9' are not in the alphabet
#guard (decode? "MZ======").isNone          -- non-zero pad bits ("MY======" is canonical)
#guard (decode? "MZXW6Y==").isNone          -- 2 is not a valid padding length
#guard (decode? "MZXW6png").isNone          -- lowercase tail
#guard (decode? "MY======MY======").isNone  -- padding before the final group
#guard (decode? "========").isNone          -- padding alone is not a group

end Rfc4648.Base32
