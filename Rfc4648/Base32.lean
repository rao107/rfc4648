import Rfc4648.Util

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

/-! ## Round-trip and canonicity

Same statements as `Rfc4648.Base16` and `Rfc4648.Base64`: strict decoding
inverts encoding, and the decoder accepts exactly the canonical encodings. -/

section RoundTrip

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

/-! Bounds on the 5-bit pieces produced by the encoder. -/

private theorem shr3_lt32 : ∀ b : UInt8, (b >>> 3).toNat < 32 :=
  uint8_all (by decide)

private theorem shr4_lt16 : ∀ b : UInt8, (b >>> 4).toNat < 16 :=
  uint8_all (by decide)

private theorem shr4_lt32 : ∀ b : UInt8, (b >>> 4).toNat < 32 :=
  uint8_all (by decide)

private theorem shr5_lt8 : ∀ b : UInt8, (b >>> 5).toNat < 8 :=
  uint8_all (by decide)

private theorem shr5_lt32 : ∀ b : UInt8, (b >>> 5).toNat < 32 :=
  uint8_all (by decide)

private theorem shr6_lt4 : ∀ b : UInt8, (b >>> 6).toNat < 4 :=
  uint8_all (by decide)

private theorem shr6_lt32 : ∀ b : UInt8, (b >>> 6).toNat < 32 :=
  uint8_all (by decide)

private theorem shr7_lt2 : ∀ b : UInt8, (b >>> 7).toNat < 2 :=
  uint8_all (by decide)

private theorem shr7_lt32 : ∀ b : UInt8, (b >>> 7).toNat < 32 :=
  uint8_all (by decide)

private theorem and1_lt2 : ∀ b : UInt8, (b &&& 0x01).toNat < 2 :=
  uint8_all (by decide)

private theorem and1_shl4_lt32 : ∀ b : UInt8, ((b &&& 0x01) <<< 4).toNat < 32 :=
  uint8_all (by decide)

private theorem and3_lt4 : ∀ b : UInt8, (b &&& 0x03).toNat < 4 :=
  uint8_all (by decide)

private theorem and3_shl3_lt32 : ∀ b : UInt8, ((b &&& 0x03) <<< 3).toNat < 32 :=
  uint8_all (by decide)

private theorem and7_lt8 : ∀ b : UInt8, (b &&& 0x07).toNat < 8 :=
  uint8_all (by decide)

private theorem and7_shl2_lt32 : ∀ b : UInt8, ((b &&& 0x07) <<< 2).toNat < 32 :=
  uint8_all (by decide)

private theorem and15_lt16 : ∀ b : UInt8, (b &&& 0x0F).toNat < 16 :=
  uint8_all (by decide)

private theorem and15_shl1_lt32 : ∀ b : UInt8, ((b &&& 0x0F) <<< 1).toNat < 32 :=
  uint8_all (by decide)

private theorem and31_lt32 : ∀ b : UInt8, (b &&& 0x1F).toNat < 32 :=
  uint8_all (by decide)

private theorem shr1_and31_lt32 : ∀ b : UInt8, ((b >>> 1) &&& 0x1F).toNat < 32 :=
  uint8_all (by decide)

private theorem shr2_and31_lt32 : ∀ b : UInt8, ((b >>> 2) &&& 0x1F).toNat < 32 :=
  uint8_all (by decide)

private theorem or_lt32 : ∀ x y : UInt8, x.toNat < 32 → y.toNat < 32 →
    (x ||| y).toNat < 32 :=
  uint8_all_lt₂ (by decide)

/-! Bounds on pieces of decoded 5-bit values. -/

private theorem shr1_lt16_of_lt32 : ∀ v : UInt8, v.toNat < 32 → (v >>> 1).toNat < 16 :=
  uint8_all (by decide)

private theorem shr2_lt8_of_lt32 : ∀ v : UInt8, v.toNat < 32 → (v >>> 2).toNat < 8 :=
  uint8_all (by decide)

private theorem shr3_lt4_of_lt32 : ∀ v : UInt8, v.toNat < 32 → (v >>> 3).toNat < 4 :=
  uint8_all (by decide)

private theorem shr4_lt2_of_lt32 : ∀ v : UInt8, v.toNat < 32 → (v >>> 4).toNat < 2 :=
  uint8_all (by decide)

/-! Splitting a byte and reassembling it. -/

private theorem recombine1 : ∀ b : UInt8, ((b >>> 1) <<< 1) ||| (b &&& 0x01) = b :=
  uint8_all (by decide)

private theorem recombine2 : ∀ b : UInt8, ((b >>> 2) <<< 2) ||| (b &&& 0x03) = b :=
  uint8_all (by decide)

private theorem recombine3 : ∀ b : UInt8, ((b >>> 3) <<< 3) ||| (b &&& 0x07) = b :=
  uint8_all (by decide)

private theorem recombine4 : ∀ b : UInt8, ((b >>> 4) <<< 4) ||| (b &&& 0x0F) = b :=
  uint8_all (by decide)

private theorem recombine5 : ∀ b : UInt8, ((b >>> 5) <<< 5) ||| (b &&& 0x1F) = b :=
  uint8_all (by decide)

private theorem recombineB1 : ∀ b : UInt8,
    (((b >>> 6) <<< 6) ||| (b &&& 0x3E)) ||| (b &&& 0x01) = b :=
  uint8_all (by decide)

private theorem recombineB3 : ∀ b : UInt8,
    (((b >>> 7) <<< 7) ||| (b &&& 0x7C)) ||| (b &&& 0x03) = b :=
  uint8_all (by decide)

private theorem shl1_mask : ∀ b : UInt8, ((b >>> 1) &&& 0x1F) <<< 1 = b &&& 0x3E :=
  uint8_all (by decide)

private theorem shl2_mask : ∀ b : UInt8, ((b >>> 2) &&& 0x1F) <<< 2 = b &&& 0x7C :=
  uint8_all (by decide)

private theorem unshl2_and7 : ∀ b : UInt8, ((b &&& 0x07) <<< 2) >>> 2 = b &&& 0x07 :=
  uint8_all (by decide)

private theorem unshl4_and1 : ∀ b : UInt8, ((b &&& 0x01) <<< 4) >>> 4 = b &&& 0x01 :=
  uint8_all (by decide)

private theorem unshl1_and15 : ∀ b : UInt8, ((b &&& 0x0F) <<< 1) >>> 1 = b &&& 0x0F :=
  uint8_all (by decide)

private theorem unshl3_and3 : ∀ b : UInt8, ((b &&& 0x03) <<< 3) >>> 3 = b &&& 0x03 :=
  uint8_all (by decide)

/-! The pad bits of a final partial group are zero. -/

private theorem padz2 : ∀ b : UInt8, ((b &&& 0x07) <<< 2) &&& 0x03 = 0 :=
  uint8_all (by decide)

private theorem padz4 : ∀ b : UInt8, ((b &&& 0x01) <<< 4) &&& 0x0F = 0 :=
  uint8_all (by decide)

private theorem padz1 : ∀ b : UInt8, ((b &&& 0x0F) <<< 1) &&& 0x01 = 0 :=
  uint8_all (by decide)

private theorem padz3 : ∀ b : UInt8, ((b &&& 0x03) <<< 3) &&& 0x07 = 0 :=
  uint8_all (by decide)

/-! Zero pad bits can be shifted out and back. -/

private theorem pad1_cancel : ∀ v : UInt8, v.toNat < 32 → v &&& 0x01 = 0 →
    (v >>> 1) <<< 1 = v :=
  uint8_all (by decide)

private theorem pad2_cancel : ∀ v : UInt8, v.toNat < 32 → v &&& 0x03 = 0 →
    (v >>> 2) <<< 2 = v :=
  uint8_all (by decide)

private theorem pad3_cancel : ∀ v : UInt8, v.toNat < 32 → v &&& 0x07 = 0 →
    (v >>> 3) <<< 3 = v :=
  uint8_all (by decide)

private theorem pad4_cancel : ∀ v : UInt8, v.toNat < 32 → v &&& 0x0F = 0 →
    (v >>> 4) <<< 4 = v :=
  uint8_all (by decide)

/-! Extracting one summand from a disjoint `|||` (encoder side). -/

private theorem or2_shr2 : ∀ x y : UInt8, x.toNat < 8 → y.toNat < 4 →
    ((x <<< 2) ||| y) >>> 2 = x :=
  uint8_all_lt₂ (by decide)

private theorem or2_shl6 : ∀ x y : UInt8, x.toNat < 8 → y.toNat < 4 →
    ((x <<< 2) ||| y) <<< 6 = y <<< 6 :=
  uint8_all_lt₂ (by decide)

private theorem or4_shr4 : ∀ x y : UInt8, x.toNat < 2 → y.toNat < 16 →
    ((x <<< 4) ||| y) >>> 4 = x :=
  uint8_all_lt₂ (by decide)

private theorem or4_shl4 : ∀ x y : UInt8, x.toNat < 2 → y.toNat < 16 →
    ((x <<< 4) ||| y) <<< 4 = y <<< 4 :=
  uint8_all_lt₂ (by decide)

private theorem or1_shr1 : ∀ x y : UInt8, x.toNat < 16 → y.toNat < 2 →
    ((x <<< 1) ||| y) >>> 1 = x :=
  uint8_all_lt₂ (by decide)

private theorem or1_shl7 : ∀ x y : UInt8, x.toNat < 16 → y.toNat < 2 →
    ((x <<< 1) ||| y) <<< 7 = y <<< 7 :=
  uint8_all_lt₂ (by decide)

private theorem or3_shr3 : ∀ x y : UInt8, x.toNat < 4 → y.toNat < 8 →
    ((x <<< 3) ||| y) >>> 3 = x :=
  uint8_all_lt₂ (by decide)

private theorem or3_shl5 : ∀ x y : UInt8, x.toNat < 4 → y.toNat < 8 →
    ((x <<< 3) ||| y) <<< 5 = y <<< 5 :=
  uint8_all_lt₂ (by decide)

/-! Extracting one summand from a disjoint `|||` (decoder side). -/

private theorem vor_shr3 : ∀ x y : UInt8, x.toNat < 32 → y.toNat < 8 →
    ((x <<< 3) ||| y) >>> 3 = x :=
  uint8_all_lt₂ (by decide)

private theorem vor_and7 : ∀ x y : UInt8, x.toNat < 32 → y.toNat < 8 →
    ((x <<< 3) ||| y) &&& 0x07 = y :=
  uint8_all_lt₂ (by decide)

private theorem vor_shr4_and15 : ∀ x y : UInt8, x.toNat < 32 → y.toNat < 16 →
    ((x <<< 4) ||| y) >>> 4 = x &&& 0x0F :=
  uint8_all_lt₂ (by decide)

private theorem vor_and15 : ∀ x y : UInt8, x.toNat < 32 → y.toNat < 16 →
    ((x <<< 4) ||| y) &&& 0x0F = y :=
  uint8_all_lt₂ (by decide)

private theorem vor_shr5_and7 : ∀ x y : UInt8, x.toNat < 32 → y.toNat < 32 →
    ((x <<< 5) ||| y) >>> 5 = x &&& 0x07 :=
  uint8_all_lt₂ (by decide)

private theorem vor_and31 : ∀ x y : UInt8, x.toNat < 32 → y.toNat < 32 →
    ((x <<< 5) ||| y) &&& 0x1F = y :=
  uint8_all_lt₂ (by decide)

private theorem vor3_shr6 : ∀ x y z : UInt8, x.toNat < 32 → y.toNat < 32 →
    z.toNat < 2 → (((x <<< 6) ||| (y <<< 1)) ||| z) >>> 6 = x &&& 0x03 :=
  uint8_all_lt₃ (by decide)

private theorem vor3_mid1 : ∀ x y z : UInt8, x.toNat < 32 → y.toNat < 32 →
    z.toNat < 2 → ((((x <<< 6) ||| (y <<< 1)) ||| z) >>> 1) &&& 0x1F = y :=
  uint8_all_lt₃ (by decide)

private theorem vor3_and1 : ∀ x y z : UInt8, x.toNat < 32 → y.toNat < 32 →
    z.toNat < 2 → (((x <<< 6) ||| (y <<< 1)) ||| z) &&& 0x01 = z :=
  uint8_all_lt₃ (by decide)

private theorem vor3_shr7 : ∀ x y z : UInt8, x.toNat < 32 → y.toNat < 32 →
    z.toNat < 4 → (((x <<< 7) ||| (y <<< 2)) ||| z) >>> 7 = x &&& 0x01 :=
  uint8_all_lt₃ (by decide)

private theorem vor3_mid2 : ∀ x y z : UInt8, x.toNat < 32 → y.toNat < 32 →
    z.toNat < 4 → ((((x <<< 7) ||| (y <<< 2)) ||| z) >>> 2) &&& 0x1F = y :=
  uint8_all_lt₃ (by decide)

private theorem vor3_and3 : ∀ x y z : UInt8, x.toNat < 32 → y.toNat < 32 →
    z.toNat < 4 → (((x <<< 7) ||| (y <<< 2)) ||| z) &&& 0x03 = z :=
  uint8_all_lt₃ (by decide)

/-! Character-map lemmas. -/

/-- `ofChar?` is a left inverse of `toChar` on 5-bit values. -/
theorem ofChar?_toChar : ∀ v : UInt8, v.toNat < 32 → ofChar? (toChar v) = some v :=
  uint8_all (by decide)

private theorem toChar_ne_pad : ∀ v : UInt8, v.toNat < 32 → toChar v ≠ '=' :=
  uint8_all (by decide)

/-- Characters accepted by `ofChar?` decode to 5-bit values, and `toChar`
maps those values back to the same character. -/
theorem ofChar?_eq_some {c : Char} {v : UInt8} (h : ofChar? c = some v) :
    v.toNat < 32 ∧ toChar v = c := by
  unfold ofChar? at h
  split at h
  case isTrue hAZ =>
    obtain ⟨hA, hZ⟩ := hAZ
    have hA' : 65 ≤ c.toNat := hA
    have hZ' : c.toNat ≤ 90 := hZ
    injection h with hv
    subst hv
    have eA : 'A'.toNat = 65 := rfl
    have hle : UInt8.ofNat 65 ≤ UInt8.ofNat c.toNat := by
      rw [UInt8.le_iff_toNat_le, UInt8.toNat_ofNat', UInt8.toNat_ofNat']
      omega
    have hval : (c.toNat.toUInt8 - 'A'.toNat.toUInt8).toNat = c.toNat - 65 := by
      simp only [Nat.toUInt8_eq, eA, UInt8.toNat_sub_of_le _ _ hle, UInt8.toNat_ofNat']
      omega
    refine ⟨by omega, ?_⟩
    unfold toChar
    rw [if_pos (show _ < (26 : UInt8) by
      rw [UInt8.lt_iff_toNat_lt, hval]; show c.toNat - 65 < 26; omega)]
    rw [hval, show 'A'.toNat + (c.toNat - 65) = c.toNat by
      show 65 + (c.toNat - 65) = c.toNat; omega]
    exact Char.ofNat_toNat c
  case isFalse =>
    split at h
    case isTrue h27 =>
      obtain ⟨h2, h7⟩ := h27
      have h2' : 50 ≤ c.toNat := h2
      have h7' : c.toNat ≤ 55 := h7
      injection h with hv
      subst hv
      have e2 : '2'.toNat = 50 := rfl
      have hle : UInt8.ofNat 50 ≤ UInt8.ofNat c.toNat := by
        rw [UInt8.le_iff_toNat_le, UInt8.toNat_ofNat', UInt8.toNat_ofNat']
        omega
      have hval : (c.toNat.toUInt8 - '2'.toNat.toUInt8 + 26).toNat = c.toNat - 24 := by
        simp only [Nat.toUInt8_eq, e2, UInt8.toNat_add, UInt8.toNat_sub_of_le _ _ hle,
          UInt8.toNat_ofNat', UInt8.toNat_ofNat]
        omega
      refine ⟨by omega, ?_⟩
      unfold toChar
      rw [if_neg (show ¬(_ < (26 : UInt8)) by
        rw [UInt8.lt_iff_toNat_lt, hval]; show ¬(c.toNat - 24 < 26); omega)]
      rw [hval, show '2'.toNat + (c.toNat - 24 - 26) = c.toNat by
        show 50 + (c.toNat - 24 - 26) = c.toNat; omega]
      exact Char.ofNat_toNat c
    case isFalse => simp at h

/-! Main theorems. -/

/-- Round-trip: strictly decoding an encoding yields the original bytes. -/
theorem decodeList_encodeList : ∀ bs : List UInt8,
    decodeList (encodeList bs) = some bs
  | [] => rfl
  | [b0] => by
    simp only [encodeList, decodeList,
      ofChar?_toChar _ (shr3_lt32 b0), ofChar?_toChar _ (and7_shl2_lt32 b0),
      Option.bind_eq_bind, Option.bind_some]
    rw [if_pos trivial,
      if_pos ⟨trivial, trivial, trivial, trivial, trivial, trivial, padz2 b0⟩,
      unshl2_and7 b0, recombine3 b0]
  | [b0, b1] => by
    have h1 : (((b0 &&& 0x07) <<< 2) ||| (b1 >>> 6)).toNat < 32 :=
      or_lt32 _ _ (and7_shl2_lt32 b0) (shr6_lt32 b1)
    simp only [encodeList, decodeList,
      ofChar?_toChar _ (shr3_lt32 b0), ofChar?_toChar _ h1,
      ofChar?_toChar _ (shr1_and31_lt32 b1), ofChar?_toChar _ (and1_shl4_lt32 b1),
      Option.bind_eq_bind, Option.bind_some]
    rw [if_neg (toChar_ne_pad _ (shr1_and31_lt32 b1)),
      if_pos trivial, if_pos ⟨trivial, trivial, trivial, trivial, padz4 b1⟩,
      or2_shr2 _ _ (and7_lt8 b0) (shr6_lt4 b1), recombine3 b0,
      or2_shl6 _ _ (and7_lt8 b0) (shr6_lt4 b1), shl1_mask b1,
      unshl4_and1 b1, recombineB1 b1]
  | [b0, b1, b2] => by
    have h1 : (((b0 &&& 0x07) <<< 2) ||| (b1 >>> 6)).toNat < 32 :=
      or_lt32 _ _ (and7_shl2_lt32 b0) (shr6_lt32 b1)
    have h3 : (((b1 &&& 0x01) <<< 4) ||| (b2 >>> 4)).toNat < 32 :=
      or_lt32 _ _ (and1_shl4_lt32 b1) (shr4_lt32 b2)
    simp only [encodeList, decodeList,
      ofChar?_toChar _ (shr3_lt32 b0), ofChar?_toChar _ h1,
      ofChar?_toChar _ (shr1_and31_lt32 b1), ofChar?_toChar _ h3,
      ofChar?_toChar _ (and15_shl1_lt32 b2),
      Option.bind_eq_bind, Option.bind_some]
    rw [if_neg (toChar_ne_pad _ (shr1_and31_lt32 b1)),
      if_neg (toChar_ne_pad _ (and15_shl1_lt32 b2)),
      if_pos trivial, if_pos ⟨trivial, trivial, trivial, padz1 b2⟩,
      or2_shr2 _ _ (and7_lt8 b0) (shr6_lt4 b1), recombine3 b0,
      or2_shl6 _ _ (and7_lt8 b0) (shr6_lt4 b1), shl1_mask b1,
      or4_shr4 _ _ (and1_lt2 b1) (shr4_lt16 b2), recombineB1 b1,
      or4_shl4 _ _ (and1_lt2 b1) (shr4_lt16 b2),
      unshl1_and15 b2, recombine4 b2]
  | [b0, b1, b2, b3] => by
    have h1 : (((b0 &&& 0x07) <<< 2) ||| (b1 >>> 6)).toNat < 32 :=
      or_lt32 _ _ (and7_shl2_lt32 b0) (shr6_lt32 b1)
    have h3 : (((b1 &&& 0x01) <<< 4) ||| (b2 >>> 4)).toNat < 32 :=
      or_lt32 _ _ (and1_shl4_lt32 b1) (shr4_lt32 b2)
    have h4 : (((b2 &&& 0x0F) <<< 1) ||| (b3 >>> 7)).toNat < 32 :=
      or_lt32 _ _ (and15_shl1_lt32 b2) (shr7_lt32 b3)
    simp only [encodeList, decodeList,
      ofChar?_toChar _ (shr3_lt32 b0), ofChar?_toChar _ h1,
      ofChar?_toChar _ (shr1_and31_lt32 b1), ofChar?_toChar _ h3,
      ofChar?_toChar _ h4, ofChar?_toChar _ (shr2_and31_lt32 b3),
      ofChar?_toChar _ (and3_shl3_lt32 b3),
      Option.bind_eq_bind, Option.bind_some]
    rw [if_neg (toChar_ne_pad _ (shr1_and31_lt32 b1)),
      if_neg (toChar_ne_pad _ h4),
      if_neg (toChar_ne_pad _ (shr2_and31_lt32 b3)),
      if_pos trivial, if_pos ⟨trivial, padz3 b3⟩,
      or2_shr2 _ _ (and7_lt8 b0) (shr6_lt4 b1), recombine3 b0,
      or2_shl6 _ _ (and7_lt8 b0) (shr6_lt4 b1), shl1_mask b1,
      or4_shr4 _ _ (and1_lt2 b1) (shr4_lt16 b2), recombineB1 b1,
      or4_shl4 _ _ (and1_lt2 b1) (shr4_lt16 b2),
      or1_shr1 _ _ (and15_lt16 b2) (shr7_lt2 b3), recombine4 b2,
      or1_shl7 _ _ (and15_lt16 b2) (shr7_lt2 b3), shl2_mask b3,
      unshl3_and3 b3, recombineB3 b3]
  | b0 :: b1 :: b2 :: b3 :: b4 :: rest => by
    have h1 : (((b0 &&& 0x07) <<< 2) ||| (b1 >>> 6)).toNat < 32 :=
      or_lt32 _ _ (and7_shl2_lt32 b0) (shr6_lt32 b1)
    have h3 : (((b1 &&& 0x01) <<< 4) ||| (b2 >>> 4)).toNat < 32 :=
      or_lt32 _ _ (and1_shl4_lt32 b1) (shr4_lt32 b2)
    have h4 : (((b2 &&& 0x0F) <<< 1) ||| (b3 >>> 7)).toNat < 32 :=
      or_lt32 _ _ (and15_shl1_lt32 b2) (shr7_lt32 b3)
    have h6 : (((b3 &&& 0x03) <<< 3) ||| (b4 >>> 5)).toNat < 32 :=
      or_lt32 _ _ (and3_shl3_lt32 b3) (shr5_lt32 b4)
    simp only [encodeList, decodeList,
      ofChar?_toChar _ (shr3_lt32 b0), ofChar?_toChar _ h1,
      ofChar?_toChar _ (shr1_and31_lt32 b1), ofChar?_toChar _ h3,
      ofChar?_toChar _ h4, ofChar?_toChar _ (shr2_and31_lt32 b3),
      ofChar?_toChar _ h6, ofChar?_toChar _ (and31_lt32 b4),
      Option.bind_eq_bind, Option.bind_some,
      decodeList_encodeList rest]
    rw [if_neg (toChar_ne_pad _ (shr1_and31_lt32 b1)),
      if_neg (toChar_ne_pad _ h4),
      if_neg (toChar_ne_pad _ (shr2_and31_lt32 b3)),
      if_neg (toChar_ne_pad _ (and31_lt32 b4)),
      or2_shr2 _ _ (and7_lt8 b0) (shr6_lt4 b1), recombine3 b0,
      or2_shl6 _ _ (and7_lt8 b0) (shr6_lt4 b1), shl1_mask b1,
      or4_shr4 _ _ (and1_lt2 b1) (shr4_lt16 b2), recombineB1 b1,
      or4_shl4 _ _ (and1_lt2 b1) (shr4_lt16 b2),
      or1_shr1 _ _ (and15_lt16 b2) (shr7_lt2 b3), recombine4 b2,
      or1_shl7 _ _ (and15_lt16 b2) (shr7_lt2 b3), shl2_mask b3,
      or3_shr3 _ _ (and3_lt4 b3) (shr5_lt8 b4), recombineB3 b3,
      or3_shl5 _ _ (and3_lt4 b3) (shr5_lt8 b4), recombine5 b4]

/-- Canonicity: every string the strict decoder accepts is the encoding of
the bytes it returns. -/
theorem encodeList_decodeList : ∀ {cs : List Char} {bs : List UInt8},
    decodeList cs = some bs → encodeList bs = cs
  | [], _, h => by
    simp only [decodeList, Option.some.injEq] at h
    simp [← h, encodeList]
  | _c0 :: _c1 :: c2 :: c3 :: c4 :: c5 :: c6 :: c7 :: rest, bs, h => by
    simp only [decodeList, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨v0, hv0, v1, hv1, h⟩ := h
    obtain ⟨hlt0, hc0⟩ := ofChar?_eq_some hv0
    obtain ⟨hlt1, hc1⟩ := ofChar?_eq_some hv1
    split at h
    case isTrue hc2 =>
      split at h
      case isTrue hcond =>
        obtain ⟨hc3, hc4, hc5, hc6, hc7, hrest, hpad⟩ := hcond
        injection h with h
        subst h
        subst hc2 hc3 hc4 hc5 hc6 hc7 hrest
        simp only [encodeList]
        rw [vor_shr3 v0 (v1 >>> 2) hlt0 (shr2_lt8_of_lt32 v1 hlt1),
          vor_and7 v0 (v1 >>> 2) hlt0 (shr2_lt8_of_lt32 v1 hlt1),
          pad2_cancel v1 hlt1 hpad, hc0, hc1]
      case isFalse => simp at h
    case isFalse hc2 =>
      simp only [Option.bind_eq_some_iff] at h
      obtain ⟨v2, hv2, v3, hv3, h⟩ := h
      obtain ⟨hlt2, hc2'⟩ := ofChar?_eq_some hv2
      obtain ⟨hlt3, hc3'⟩ := ofChar?_eq_some hv3
      split at h
      case isTrue hc4 =>
        split at h
        case isTrue hcond =>
          obtain ⟨hc5, hc6, hc7, hrest, hpad⟩ := hcond
          injection h with h
          subst h
          subst hc4 hc5 hc6 hc7 hrest
          simp only [encodeList]
          rw [vor_shr3 v0 (v1 >>> 2) hlt0 (shr2_lt8_of_lt32 v1 hlt1),
            vor_and7 v0 (v1 >>> 2) hlt0 (shr2_lt8_of_lt32 v1 hlt1),
            vor3_shr6 v1 v2 (v3 >>> 4) hlt1 hlt2 (shr4_lt2_of_lt32 v3 hlt3),
            recombine2 v1,
            vor3_mid1 v1 v2 (v3 >>> 4) hlt1 hlt2 (shr4_lt2_of_lt32 v3 hlt3),
            vor3_and1 v1 v2 (v3 >>> 4) hlt1 hlt2 (shr4_lt2_of_lt32 v3 hlt3),
            pad4_cancel v3 hlt3 hpad, hc0, hc1, hc2', hc3']
        case isFalse => simp at h
      case isFalse hc4 =>
        simp only [Option.bind_eq_some_iff] at h
        obtain ⟨v4, hv4, h⟩ := h
        obtain ⟨hlt4, hc4'⟩ := ofChar?_eq_some hv4
        split at h
        case isTrue hc5 =>
          split at h
          case isTrue hcond =>
            obtain ⟨hc6, hc7, hrest, hpad⟩ := hcond
            injection h with h
            subst h
            subst hc5 hc6 hc7 hrest
            simp only [encodeList]
            rw [vor_shr3 v0 (v1 >>> 2) hlt0 (shr2_lt8_of_lt32 v1 hlt1),
              vor_and7 v0 (v1 >>> 2) hlt0 (shr2_lt8_of_lt32 v1 hlt1),
              vor3_shr6 v1 v2 (v3 >>> 4) hlt1 hlt2 (shr4_lt2_of_lt32 v3 hlt3),
              recombine2 v1,
              vor3_mid1 v1 v2 (v3 >>> 4) hlt1 hlt2 (shr4_lt2_of_lt32 v3 hlt3),
              vor3_and1 v1 v2 (v3 >>> 4) hlt1 hlt2 (shr4_lt2_of_lt32 v3 hlt3),
              vor_shr4_and15 v3 (v4 >>> 1) hlt3 (shr1_lt16_of_lt32 v4 hlt4),
              recombine4 v3,
              vor_and15 v3 (v4 >>> 1) hlt3 (shr1_lt16_of_lt32 v4 hlt4),
              pad1_cancel v4 hlt4 hpad, hc0, hc1, hc2', hc3', hc4']
          case isFalse => simp at h
        case isFalse hc5 =>
          simp only [Option.bind_eq_some_iff] at h
          obtain ⟨v5, hv5, v6, hv6, h⟩ := h
          obtain ⟨hlt5, hc5'⟩ := ofChar?_eq_some hv5
          obtain ⟨hlt6, hc6'⟩ := ofChar?_eq_some hv6
          split at h
          case isTrue hc7 =>
            split at h
            case isTrue hcond =>
              obtain ⟨hrest, hpad⟩ := hcond
              injection h with h
              subst h
              subst hc7 hrest
              simp only [encodeList]
              rw [vor_shr3 v0 (v1 >>> 2) hlt0 (shr2_lt8_of_lt32 v1 hlt1),
                vor_and7 v0 (v1 >>> 2) hlt0 (shr2_lt8_of_lt32 v1 hlt1),
                vor3_shr6 v1 v2 (v3 >>> 4) hlt1 hlt2 (shr4_lt2_of_lt32 v3 hlt3),
                recombine2 v1,
                vor3_mid1 v1 v2 (v3 >>> 4) hlt1 hlt2 (shr4_lt2_of_lt32 v3 hlt3),
                vor3_and1 v1 v2 (v3 >>> 4) hlt1 hlt2 (shr4_lt2_of_lt32 v3 hlt3),
                vor_shr4_and15 v3 (v4 >>> 1) hlt3 (shr1_lt16_of_lt32 v4 hlt4),
                recombine4 v3,
                vor_and15 v3 (v4 >>> 1) hlt3 (shr1_lt16_of_lt32 v4 hlt4),
                vor3_shr7 v4 v5 (v6 >>> 3) hlt4 hlt5 (shr3_lt4_of_lt32 v6 hlt6),
                recombine1 v4,
                vor3_mid2 v4 v5 (v6 >>> 3) hlt4 hlt5 (shr3_lt4_of_lt32 v6 hlt6),
                vor3_and3 v4 v5 (v6 >>> 3) hlt4 hlt5 (shr3_lt4_of_lt32 v6 hlt6),
                pad3_cancel v6 hlt6 hpad, hc0, hc1, hc2', hc3', hc4', hc5', hc6']
            case isFalse => simp at h
          case isFalse hc7 =>
            simp only [Option.bind_eq_some_iff, Option.some.injEq] at h
            obtain ⟨v7, hv7, tail, htail, hbs⟩ := h
            obtain ⟨hlt7, hc7'⟩ := ofChar?_eq_some hv7
            subst hbs
            simp only [encodeList]
            rw [vor_shr3 v0 (v1 >>> 2) hlt0 (shr2_lt8_of_lt32 v1 hlt1),
              vor_and7 v0 (v1 >>> 2) hlt0 (shr2_lt8_of_lt32 v1 hlt1),
              vor3_shr6 v1 v2 (v3 >>> 4) hlt1 hlt2 (shr4_lt2_of_lt32 v3 hlt3),
              recombine2 v1,
              vor3_mid1 v1 v2 (v3 >>> 4) hlt1 hlt2 (shr4_lt2_of_lt32 v3 hlt3),
              vor3_and1 v1 v2 (v3 >>> 4) hlt1 hlt2 (shr4_lt2_of_lt32 v3 hlt3),
              vor_shr4_and15 v3 (v4 >>> 1) hlt3 (shr1_lt16_of_lt32 v4 hlt4),
              recombine4 v3,
              vor_and15 v3 (v4 >>> 1) hlt3 (shr1_lt16_of_lt32 v4 hlt4),
              vor3_shr7 v4 v5 (v6 >>> 3) hlt4 hlt5 (shr3_lt4_of_lt32 v6 hlt6),
              recombine1 v4,
              vor3_mid2 v4 v5 (v6 >>> 3) hlt4 hlt5 (shr3_lt4_of_lt32 v6 hlt6),
              vor3_and3 v4 v5 (v6 >>> 3) hlt4 hlt5 (shr3_lt4_of_lt32 v6 hlt6),
              vor_shr5_and7 v6 v7 hlt6 hlt7,
              recombine3 v6,
              vor_and31 v6 v7 hlt6 hlt7,
              encodeList_decodeList htail,
              hc0, hc1, hc2', hc3', hc4', hc5', hc6', hc7']
  | [_], _, h => by simp [decodeList] at h
  | [_, _], _, h => by simp [decodeList] at h
  | [_, _, _], _, h => by simp [decodeList] at h
  | [_, _, _, _], _, h => by simp [decodeList] at h
  | [_, _, _, _, _], _, h => by simp [decodeList] at h
  | [_, _, _, _, _, _], _, h => by simp [decodeList] at h
  | [_, _, _, _, _, _, _], _, h => by simp [decodeList] at h

/-- Round-trip, lifted to `ByteArray`/`String`. -/
theorem decode?_encode (data : ByteArray) : decode? (encode data) = some data := by
  simp only [decode?, encode, String.toList_ofList, decodeList_encodeList,
    Option.map_some, ByteArray.mk_toList_toArray]

/-- Canonicity, lifted to `ByteArray`/`String`. -/
theorem encode_decode? {s : String} {data : ByteArray}
    (h : decode? s = some data) : encode data = s := by
  simp only [decode?, Option.map_eq_some_iff] at h
  obtain ⟨l, hl, hdata⟩ := h
  subst hdata
  simp only [encode, ByteArray.toList_mk]
  rw [encodeList_decodeList hl, String.ofList_toList]

end RoundTrip

/-! ## Output length

Encoding `n` bytes yields `8 * ⌈n / 5⌉` characters (RFC 4648 §6: every
5-byte group, including a padded final partial group, becomes 8
characters), so valid encodings always have length divisible by 8. -/

section Length

/-- The encoding of `n` bytes has exactly `8 * ((n + 4) / 5)` characters. -/
theorem length_encodeList : ∀ bs : List UInt8,
    (encodeList bs).length = 8 * ((bs.length + 4) / 5)
  | [] => rfl
  | [_] => by simp [encodeList]
  | [_, _] => by simp [encodeList]
  | [_, _, _] => by simp [encodeList]
  | [_, _, _, _] => by simp [encodeList]
  | b0 :: b1 :: b2 :: b3 :: b4 :: rest => by
    simp only [encodeList, List.length_cons, length_encodeList rest]
    omega

/-- Anything the strict decoder accepts has the padded encoding length of
its output. -/
theorem length_of_decodeList {cs : List Char} {bs : List UInt8}
    (h : decodeList cs = some bs) : cs.length = 8 * ((bs.length + 4) / 5) := by
  rw [← encodeList_decodeList h, length_encodeList]

/-- Anything the strict decoder accepts has length divisible by 8. -/
theorem length_of_decodeList_mod {cs : List Char} {bs : List UInt8}
    (h : decodeList cs = some bs) : cs.length % 8 = 0 := by
  rw [length_of_decodeList h]
  omega

/-- Encoding length, lifted to `ByteArray`/`String`. -/
theorem length_encode (data : ByteArray) :
    (encode data).length = 8 * ((data.size + 4) / 5) := by
  rw [encode, String.length_ofList, length_encodeList, ByteArray.length_toList]

/-- Decoding length, lifted to `ByteArray`/`String`. -/
theorem length_of_decode? {s : String} {data : ByteArray}
    (h : decode? s = some data) : s.length = 8 * ((data.size + 4) / 5) := by
  rw [← encode_decode? h, length_encode]

end Length

/-! ## RFC 4648 §7 — Base 32 with extended hex alphabet

Identical to base32 except for the alphabet: `0`–`9`, `A`–`V`, chosen so
that encoded data sorts in the same order as the underlying bytes. All
bit-level lemmas are shared with the §6 codec; only the character maps
and their three lemmas differ. -/

namespace Hex

/-- Map a 5-bit value to its character in the base32hex alphabet
(RFC 4648 Table 4): `0`–`9`, `A`–`V`. -/
def toChar (v : UInt8) : Char :=
  if v < 10 then Char.ofNat ('0'.toNat + v.toNat)
  else Char.ofNat ('A'.toNat + (v.toNat - 10))

/-- Map a character to its 5-bit value, or `none` if it is not in the
base32hex alphabet. Inverse of `toChar`. -/
def ofChar? (c : Char) : Option UInt8 :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat.toUInt8 - '0'.toNat.toUInt8)
  else if 'A' ≤ c ∧ c ≤ 'V' then some (c.toNat.toUInt8 - 'A'.toNat.toUInt8 + 10)
  else none

/-- Encode bytes as base32hex characters (RFC 4648 §7). Same grouping as
`Base32.encodeList`. -/
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

/-- Strictly decode base32hex characters. Same structure as
`Base32.decodeList`. -/
def decodeList : List Char → Option (List UInt8)
  | [] => some []
  | c0 :: c1 :: c2 :: c3 :: c4 :: c5 :: c6 :: c7 :: rest => do
    let v0 ← ofChar? c0
    let v1 ← ofChar? c1
    if c2 = '=' then
      if c3 = '=' ∧ c4 = '=' ∧ c5 = '=' ∧ c6 = '=' ∧ c7 = '=' ∧ rest = [] ∧
          v1 &&& 0x03 = 0 then
        some [(v0 <<< 3) ||| (v1 >>> 2)]
      else none
    else do
      let v2 ← ofChar? c2
      let v3 ← ofChar? c3
      if c4 = '=' then
        if c5 = '=' ∧ c6 = '=' ∧ c7 = '=' ∧ rest = [] ∧ v3 &&& 0x0F = 0 then
          some [(v0 <<< 3) ||| (v1 >>> 2),
                (v1 <<< 6) ||| (v2 <<< 1) ||| (v3 >>> 4)]
        else none
      else do
        let v4 ← ofChar? c4
        if c5 = '=' then
          if c6 = '=' ∧ c7 = '=' ∧ rest = [] ∧ v4 &&& 0x01 = 0 then
            some [(v0 <<< 3) ||| (v1 >>> 2),
                  (v1 <<< 6) ||| (v2 <<< 1) ||| (v3 >>> 4),
                  (v3 <<< 4) ||| (v4 >>> 1)]
          else none
        else do
          let v5 ← ofChar? c5
          let v6 ← ofChar? c6
          if c7 = '=' then
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

/-- Encode a byte array as a base32hex string (RFC 4648 §7, with padding). -/
def encode (data : ByteArray) : String :=
  String.ofList (encodeList data.toList)

/-- Strictly decode a base32hex string. Returns `none` if the input is not
a canonical RFC 4648 §7 encoding. -/
def decode? (s : String) : Option ByteArray :=
  (decodeList s.toList).map fun bytes => ByteArray.mk bytes.toArray

/-! Test vectors (RFC 4648 §10). -/

#guard encode "".toUTF8 = ""
#guard encode "f".toUTF8 = "CO======"
#guard encode "fo".toUTF8 = "CPNG===="
#guard encode "foo".toUTF8 = "CPNMU==="
#guard encode "foob".toUTF8 = "CPNMUOG="
#guard encode "fooba".toUTF8 = "CPNMUOJ1"
#guard encode "foobar".toUTF8 = "CPNMUOJ1E8======"

#guard (decode? "").map ByteArray.toList = some "".toUTF8.toList
#guard (decode? "CO======").map ByteArray.toList = some "f".toUTF8.toList
#guard (decode? "CPNMUOJ1E8======").map ByteArray.toList = some "foobar".toUTF8.toList

#guard (decode? "co======").isNone   -- lowercase is not canonical
#guard (decode? "MY======").isNone   -- §6 alphabet ('Y') is rejected
#guard (decode? "CP======").isNone   -- non-zero pad bits

section RoundTrip

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

/-- `ofChar?` is a left inverse of `toChar` on 5-bit values. -/
theorem ofChar?_toChar : ∀ v : UInt8, v.toNat < 32 → ofChar? (toChar v) = some v :=
  uint8_all (by decide)

private theorem toChar_ne_pad : ∀ v : UInt8, v.toNat < 32 → toChar v ≠ '=' :=
  uint8_all (by decide)

/-- Characters accepted by `ofChar?` decode to 5-bit values, and `toChar`
maps those values back to the same character. -/
theorem ofChar?_eq_some {c : Char} {v : UInt8} (h : ofChar? c = some v) :
    v.toNat < 32 ∧ toChar v = c := by
  unfold ofChar? at h
  split at h
  case isTrue h09 =>
    obtain ⟨h0, h9⟩ := h09
    have h0' : 48 ≤ c.toNat := h0
    have h9' : c.toNat ≤ 57 := h9
    injection h with hv
    subst hv
    have e0 : '0'.toNat = 48 := rfl
    have hle : UInt8.ofNat 48 ≤ UInt8.ofNat c.toNat := by
      rw [UInt8.le_iff_toNat_le, UInt8.toNat_ofNat', UInt8.toNat_ofNat']
      omega
    have hval : (c.toNat.toUInt8 - '0'.toNat.toUInt8).toNat = c.toNat - 48 := by
      simp only [Nat.toUInt8_eq, e0, UInt8.toNat_sub_of_le _ _ hle, UInt8.toNat_ofNat']
      omega
    refine ⟨by omega, ?_⟩
    unfold toChar
    rw [if_pos (show _ < (10 : UInt8) by
      rw [UInt8.lt_iff_toNat_lt, hval]; show c.toNat - 48 < 10; omega)]
    rw [hval, show '0'.toNat + (c.toNat - 48) = c.toNat by
      show 48 + (c.toNat - 48) = c.toNat; omega]
    exact Char.ofNat_toNat c
  case isFalse =>
    split at h
    case isTrue hAV =>
      obtain ⟨hA, hV⟩ := hAV
      have hA' : 65 ≤ c.toNat := hA
      have hV' : c.toNat ≤ 86 := hV
      injection h with hv
      subst hv
      have eA : 'A'.toNat = 65 := rfl
      have hle : UInt8.ofNat 65 ≤ UInt8.ofNat c.toNat := by
        rw [UInt8.le_iff_toNat_le, UInt8.toNat_ofNat', UInt8.toNat_ofNat']
        omega
      have hval : (c.toNat.toUInt8 - 'A'.toNat.toUInt8 + 10).toNat = c.toNat - 55 := by
        simp only [Nat.toUInt8_eq, eA, UInt8.toNat_add, UInt8.toNat_sub_of_le _ _ hle,
          UInt8.toNat_ofNat', UInt8.toNat_ofNat]
        omega
      refine ⟨by omega, ?_⟩
      unfold toChar
      rw [if_neg (show ¬(_ < (10 : UInt8)) by
        rw [UInt8.lt_iff_toNat_lt, hval]; show ¬(c.toNat - 55 < 10); omega)]
      rw [hval, show 'A'.toNat + (c.toNat - 55 - 10) = c.toNat by
        show 65 + (c.toNat - 55 - 10) = c.toNat; omega]
      exact Char.ofNat_toNat c
    case isFalse => simp at h

/-- Round-trip: strictly decoding an encoding yields the original bytes. -/
theorem decodeList_encodeList : ∀ bs : List UInt8,
    decodeList (encodeList bs) = some bs
  | [] => rfl
  | [b0] => by
    simp only [encodeList, decodeList,
      ofChar?_toChar _ (shr3_lt32 b0), ofChar?_toChar _ (and7_shl2_lt32 b0),
      Option.bind_eq_bind, Option.bind_some]
    rw [if_pos trivial,
      if_pos ⟨trivial, trivial, trivial, trivial, trivial, trivial, padz2 b0⟩,
      unshl2_and7 b0, recombine3 b0]
  | [b0, b1] => by
    have h1 : (((b0 &&& 0x07) <<< 2) ||| (b1 >>> 6)).toNat < 32 :=
      or_lt32 _ _ (and7_shl2_lt32 b0) (shr6_lt32 b1)
    simp only [encodeList, decodeList,
      ofChar?_toChar _ (shr3_lt32 b0), ofChar?_toChar _ h1,
      ofChar?_toChar _ (shr1_and31_lt32 b1), ofChar?_toChar _ (and1_shl4_lt32 b1),
      Option.bind_eq_bind, Option.bind_some]
    rw [if_neg (toChar_ne_pad _ (shr1_and31_lt32 b1)),
      if_pos trivial, if_pos ⟨trivial, trivial, trivial, trivial, padz4 b1⟩,
      or2_shr2 _ _ (and7_lt8 b0) (shr6_lt4 b1), recombine3 b0,
      or2_shl6 _ _ (and7_lt8 b0) (shr6_lt4 b1), shl1_mask b1,
      unshl4_and1 b1, recombineB1 b1]
  | [b0, b1, b2] => by
    have h1 : (((b0 &&& 0x07) <<< 2) ||| (b1 >>> 6)).toNat < 32 :=
      or_lt32 _ _ (and7_shl2_lt32 b0) (shr6_lt32 b1)
    have h3 : (((b1 &&& 0x01) <<< 4) ||| (b2 >>> 4)).toNat < 32 :=
      or_lt32 _ _ (and1_shl4_lt32 b1) (shr4_lt32 b2)
    simp only [encodeList, decodeList,
      ofChar?_toChar _ (shr3_lt32 b0), ofChar?_toChar _ h1,
      ofChar?_toChar _ (shr1_and31_lt32 b1), ofChar?_toChar _ h3,
      ofChar?_toChar _ (and15_shl1_lt32 b2),
      Option.bind_eq_bind, Option.bind_some]
    rw [if_neg (toChar_ne_pad _ (shr1_and31_lt32 b1)),
      if_neg (toChar_ne_pad _ (and15_shl1_lt32 b2)),
      if_pos trivial, if_pos ⟨trivial, trivial, trivial, padz1 b2⟩,
      or2_shr2 _ _ (and7_lt8 b0) (shr6_lt4 b1), recombine3 b0,
      or2_shl6 _ _ (and7_lt8 b0) (shr6_lt4 b1), shl1_mask b1,
      or4_shr4 _ _ (and1_lt2 b1) (shr4_lt16 b2), recombineB1 b1,
      or4_shl4 _ _ (and1_lt2 b1) (shr4_lt16 b2),
      unshl1_and15 b2, recombine4 b2]
  | [b0, b1, b2, b3] => by
    have h1 : (((b0 &&& 0x07) <<< 2) ||| (b1 >>> 6)).toNat < 32 :=
      or_lt32 _ _ (and7_shl2_lt32 b0) (shr6_lt32 b1)
    have h3 : (((b1 &&& 0x01) <<< 4) ||| (b2 >>> 4)).toNat < 32 :=
      or_lt32 _ _ (and1_shl4_lt32 b1) (shr4_lt32 b2)
    have h4 : (((b2 &&& 0x0F) <<< 1) ||| (b3 >>> 7)).toNat < 32 :=
      or_lt32 _ _ (and15_shl1_lt32 b2) (shr7_lt32 b3)
    simp only [encodeList, decodeList,
      ofChar?_toChar _ (shr3_lt32 b0), ofChar?_toChar _ h1,
      ofChar?_toChar _ (shr1_and31_lt32 b1), ofChar?_toChar _ h3,
      ofChar?_toChar _ h4, ofChar?_toChar _ (shr2_and31_lt32 b3),
      ofChar?_toChar _ (and3_shl3_lt32 b3),
      Option.bind_eq_bind, Option.bind_some]
    rw [if_neg (toChar_ne_pad _ (shr1_and31_lt32 b1)),
      if_neg (toChar_ne_pad _ h4),
      if_neg (toChar_ne_pad _ (shr2_and31_lt32 b3)),
      if_pos trivial, if_pos ⟨trivial, padz3 b3⟩,
      or2_shr2 _ _ (and7_lt8 b0) (shr6_lt4 b1), recombine3 b0,
      or2_shl6 _ _ (and7_lt8 b0) (shr6_lt4 b1), shl1_mask b1,
      or4_shr4 _ _ (and1_lt2 b1) (shr4_lt16 b2), recombineB1 b1,
      or4_shl4 _ _ (and1_lt2 b1) (shr4_lt16 b2),
      or1_shr1 _ _ (and15_lt16 b2) (shr7_lt2 b3), recombine4 b2,
      or1_shl7 _ _ (and15_lt16 b2) (shr7_lt2 b3), shl2_mask b3,
      unshl3_and3 b3, recombineB3 b3]
  | b0 :: b1 :: b2 :: b3 :: b4 :: rest => by
    have h1 : (((b0 &&& 0x07) <<< 2) ||| (b1 >>> 6)).toNat < 32 :=
      or_lt32 _ _ (and7_shl2_lt32 b0) (shr6_lt32 b1)
    have h3 : (((b1 &&& 0x01) <<< 4) ||| (b2 >>> 4)).toNat < 32 :=
      or_lt32 _ _ (and1_shl4_lt32 b1) (shr4_lt32 b2)
    have h4 : (((b2 &&& 0x0F) <<< 1) ||| (b3 >>> 7)).toNat < 32 :=
      or_lt32 _ _ (and15_shl1_lt32 b2) (shr7_lt32 b3)
    have h6 : (((b3 &&& 0x03) <<< 3) ||| (b4 >>> 5)).toNat < 32 :=
      or_lt32 _ _ (and3_shl3_lt32 b3) (shr5_lt32 b4)
    simp only [encodeList, decodeList,
      ofChar?_toChar _ (shr3_lt32 b0), ofChar?_toChar _ h1,
      ofChar?_toChar _ (shr1_and31_lt32 b1), ofChar?_toChar _ h3,
      ofChar?_toChar _ h4, ofChar?_toChar _ (shr2_and31_lt32 b3),
      ofChar?_toChar _ h6, ofChar?_toChar _ (and31_lt32 b4),
      Option.bind_eq_bind, Option.bind_some,
      decodeList_encodeList rest]
    rw [if_neg (toChar_ne_pad _ (shr1_and31_lt32 b1)),
      if_neg (toChar_ne_pad _ h4),
      if_neg (toChar_ne_pad _ (shr2_and31_lt32 b3)),
      if_neg (toChar_ne_pad _ (and31_lt32 b4)),
      or2_shr2 _ _ (and7_lt8 b0) (shr6_lt4 b1), recombine3 b0,
      or2_shl6 _ _ (and7_lt8 b0) (shr6_lt4 b1), shl1_mask b1,
      or4_shr4 _ _ (and1_lt2 b1) (shr4_lt16 b2), recombineB1 b1,
      or4_shl4 _ _ (and1_lt2 b1) (shr4_lt16 b2),
      or1_shr1 _ _ (and15_lt16 b2) (shr7_lt2 b3), recombine4 b2,
      or1_shl7 _ _ (and15_lt16 b2) (shr7_lt2 b3), shl2_mask b3,
      or3_shr3 _ _ (and3_lt4 b3) (shr5_lt8 b4), recombineB3 b3,
      or3_shl5 _ _ (and3_lt4 b3) (shr5_lt8 b4), recombine5 b4]

/-- Canonicity: every string the strict decoder accepts is the encoding of
the bytes it returns. -/
theorem encodeList_decodeList : ∀ {cs : List Char} {bs : List UInt8},
    decodeList cs = some bs → encodeList bs = cs
  | [], _, h => by
    simp only [decodeList, Option.some.injEq] at h
    simp [← h, encodeList]
  | _c0 :: _c1 :: c2 :: c3 :: c4 :: c5 :: c6 :: c7 :: rest, bs, h => by
    simp only [decodeList, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨v0, hv0, v1, hv1, h⟩ := h
    obtain ⟨hlt0, hc0⟩ := ofChar?_eq_some hv0
    obtain ⟨hlt1, hc1⟩ := ofChar?_eq_some hv1
    split at h
    case isTrue hc2 =>
      split at h
      case isTrue hcond =>
        obtain ⟨hc3, hc4, hc5, hc6, hc7, hrest, hpad⟩ := hcond
        injection h with h
        subst h
        subst hc2 hc3 hc4 hc5 hc6 hc7 hrest
        simp only [encodeList]
        rw [vor_shr3 v0 (v1 >>> 2) hlt0 (shr2_lt8_of_lt32 v1 hlt1),
          vor_and7 v0 (v1 >>> 2) hlt0 (shr2_lt8_of_lt32 v1 hlt1),
          pad2_cancel v1 hlt1 hpad, hc0, hc1]
      case isFalse => simp at h
    case isFalse hc2 =>
      simp only [Option.bind_eq_some_iff] at h
      obtain ⟨v2, hv2, v3, hv3, h⟩ := h
      obtain ⟨hlt2, hc2'⟩ := ofChar?_eq_some hv2
      obtain ⟨hlt3, hc3'⟩ := ofChar?_eq_some hv3
      split at h
      case isTrue hc4 =>
        split at h
        case isTrue hcond =>
          obtain ⟨hc5, hc6, hc7, hrest, hpad⟩ := hcond
          injection h with h
          subst h
          subst hc4 hc5 hc6 hc7 hrest
          simp only [encodeList]
          rw [vor_shr3 v0 (v1 >>> 2) hlt0 (shr2_lt8_of_lt32 v1 hlt1),
            vor_and7 v0 (v1 >>> 2) hlt0 (shr2_lt8_of_lt32 v1 hlt1),
            vor3_shr6 v1 v2 (v3 >>> 4) hlt1 hlt2 (shr4_lt2_of_lt32 v3 hlt3),
            recombine2 v1,
            vor3_mid1 v1 v2 (v3 >>> 4) hlt1 hlt2 (shr4_lt2_of_lt32 v3 hlt3),
            vor3_and1 v1 v2 (v3 >>> 4) hlt1 hlt2 (shr4_lt2_of_lt32 v3 hlt3),
            pad4_cancel v3 hlt3 hpad, hc0, hc1, hc2', hc3']
        case isFalse => simp at h
      case isFalse hc4 =>
        simp only [Option.bind_eq_some_iff] at h
        obtain ⟨v4, hv4, h⟩ := h
        obtain ⟨hlt4, hc4'⟩ := ofChar?_eq_some hv4
        split at h
        case isTrue hc5 =>
          split at h
          case isTrue hcond =>
            obtain ⟨hc6, hc7, hrest, hpad⟩ := hcond
            injection h with h
            subst h
            subst hc5 hc6 hc7 hrest
            simp only [encodeList]
            rw [vor_shr3 v0 (v1 >>> 2) hlt0 (shr2_lt8_of_lt32 v1 hlt1),
              vor_and7 v0 (v1 >>> 2) hlt0 (shr2_lt8_of_lt32 v1 hlt1),
              vor3_shr6 v1 v2 (v3 >>> 4) hlt1 hlt2 (shr4_lt2_of_lt32 v3 hlt3),
              recombine2 v1,
              vor3_mid1 v1 v2 (v3 >>> 4) hlt1 hlt2 (shr4_lt2_of_lt32 v3 hlt3),
              vor3_and1 v1 v2 (v3 >>> 4) hlt1 hlt2 (shr4_lt2_of_lt32 v3 hlt3),
              vor_shr4_and15 v3 (v4 >>> 1) hlt3 (shr1_lt16_of_lt32 v4 hlt4),
              recombine4 v3,
              vor_and15 v3 (v4 >>> 1) hlt3 (shr1_lt16_of_lt32 v4 hlt4),
              pad1_cancel v4 hlt4 hpad, hc0, hc1, hc2', hc3', hc4']
          case isFalse => simp at h
        case isFalse hc5 =>
          simp only [Option.bind_eq_some_iff] at h
          obtain ⟨v5, hv5, v6, hv6, h⟩ := h
          obtain ⟨hlt5, hc5'⟩ := ofChar?_eq_some hv5
          obtain ⟨hlt6, hc6'⟩ := ofChar?_eq_some hv6
          split at h
          case isTrue hc7 =>
            split at h
            case isTrue hcond =>
              obtain ⟨hrest, hpad⟩ := hcond
              injection h with h
              subst h
              subst hc7 hrest
              simp only [encodeList]
              rw [vor_shr3 v0 (v1 >>> 2) hlt0 (shr2_lt8_of_lt32 v1 hlt1),
                vor_and7 v0 (v1 >>> 2) hlt0 (shr2_lt8_of_lt32 v1 hlt1),
                vor3_shr6 v1 v2 (v3 >>> 4) hlt1 hlt2 (shr4_lt2_of_lt32 v3 hlt3),
                recombine2 v1,
                vor3_mid1 v1 v2 (v3 >>> 4) hlt1 hlt2 (shr4_lt2_of_lt32 v3 hlt3),
                vor3_and1 v1 v2 (v3 >>> 4) hlt1 hlt2 (shr4_lt2_of_lt32 v3 hlt3),
                vor_shr4_and15 v3 (v4 >>> 1) hlt3 (shr1_lt16_of_lt32 v4 hlt4),
                recombine4 v3,
                vor_and15 v3 (v4 >>> 1) hlt3 (shr1_lt16_of_lt32 v4 hlt4),
                vor3_shr7 v4 v5 (v6 >>> 3) hlt4 hlt5 (shr3_lt4_of_lt32 v6 hlt6),
                recombine1 v4,
                vor3_mid2 v4 v5 (v6 >>> 3) hlt4 hlt5 (shr3_lt4_of_lt32 v6 hlt6),
                vor3_and3 v4 v5 (v6 >>> 3) hlt4 hlt5 (shr3_lt4_of_lt32 v6 hlt6),
                pad3_cancel v6 hlt6 hpad, hc0, hc1, hc2', hc3', hc4', hc5', hc6']
            case isFalse => simp at h
          case isFalse hc7 =>
            simp only [Option.bind_eq_some_iff, Option.some.injEq] at h
            obtain ⟨v7, hv7, tail, htail, hbs⟩ := h
            obtain ⟨hlt7, hc7'⟩ := ofChar?_eq_some hv7
            subst hbs
            simp only [encodeList]
            rw [vor_shr3 v0 (v1 >>> 2) hlt0 (shr2_lt8_of_lt32 v1 hlt1),
              vor_and7 v0 (v1 >>> 2) hlt0 (shr2_lt8_of_lt32 v1 hlt1),
              vor3_shr6 v1 v2 (v3 >>> 4) hlt1 hlt2 (shr4_lt2_of_lt32 v3 hlt3),
              recombine2 v1,
              vor3_mid1 v1 v2 (v3 >>> 4) hlt1 hlt2 (shr4_lt2_of_lt32 v3 hlt3),
              vor3_and1 v1 v2 (v3 >>> 4) hlt1 hlt2 (shr4_lt2_of_lt32 v3 hlt3),
              vor_shr4_and15 v3 (v4 >>> 1) hlt3 (shr1_lt16_of_lt32 v4 hlt4),
              recombine4 v3,
              vor_and15 v3 (v4 >>> 1) hlt3 (shr1_lt16_of_lt32 v4 hlt4),
              vor3_shr7 v4 v5 (v6 >>> 3) hlt4 hlt5 (shr3_lt4_of_lt32 v6 hlt6),
              recombine1 v4,
              vor3_mid2 v4 v5 (v6 >>> 3) hlt4 hlt5 (shr3_lt4_of_lt32 v6 hlt6),
              vor3_and3 v4 v5 (v6 >>> 3) hlt4 hlt5 (shr3_lt4_of_lt32 v6 hlt6),
              vor_shr5_and7 v6 v7 hlt6 hlt7,
              recombine3 v6,
              vor_and31 v6 v7 hlt6 hlt7,
              encodeList_decodeList htail,
              hc0, hc1, hc2', hc3', hc4', hc5', hc6', hc7']
  | [_], _, h => by simp [decodeList] at h
  | [_, _], _, h => by simp [decodeList] at h
  | [_, _, _], _, h => by simp [decodeList] at h
  | [_, _, _, _], _, h => by simp [decodeList] at h
  | [_, _, _, _, _], _, h => by simp [decodeList] at h
  | [_, _, _, _, _, _], _, h => by simp [decodeList] at h
  | [_, _, _, _, _, _, _], _, h => by simp [decodeList] at h

/-- Round-trip, lifted to `ByteArray`/`String`. -/
theorem decode?_encode (data : ByteArray) : decode? (encode data) = some data := by
  simp only [decode?, encode, String.toList_ofList, decodeList_encodeList,
    Option.map_some, ByteArray.mk_toList_toArray]

/-- Canonicity, lifted to `ByteArray`/`String`. -/
theorem encode_decode? {s : String} {data : ByteArray}
    (h : decode? s = some data) : encode data = s := by
  simp only [decode?, Option.map_eq_some_iff] at h
  obtain ⟨l, hl, hdata⟩ := h
  subst hdata
  simp only [encode, ByteArray.toList_mk]
  rw [encodeList_decodeList hl, String.ofList_toList]

end RoundTrip

section Length

/-- The encoding of `n` bytes has exactly `8 * ((n + 4) / 5)` characters. -/
theorem length_encodeList : ∀ bs : List UInt8,
    (encodeList bs).length = 8 * ((bs.length + 4) / 5)
  | [] => rfl
  | [_] => by simp [encodeList]
  | [_, _] => by simp [encodeList]
  | [_, _, _] => by simp [encodeList]
  | [_, _, _, _] => by simp [encodeList]
  | b0 :: b1 :: b2 :: b3 :: b4 :: rest => by
    simp only [encodeList, List.length_cons, length_encodeList rest]
    omega

/-- Anything the strict decoder accepts has the padded encoding length of
its output. -/
theorem length_of_decodeList {cs : List Char} {bs : List UInt8}
    (h : decodeList cs = some bs) : cs.length = 8 * ((bs.length + 4) / 5) := by
  rw [← encodeList_decodeList h, length_encodeList]

/-- Anything the strict decoder accepts has length divisible by 8. -/
theorem length_of_decodeList_mod {cs : List Char} {bs : List UInt8}
    (h : decodeList cs = some bs) : cs.length % 8 = 0 := by
  rw [length_of_decodeList h]
  omega

/-- Encoding length, lifted to `ByteArray`/`String`. -/
theorem length_encode (data : ByteArray) :
    (encode data).length = 8 * ((data.size + 4) / 5) := by
  rw [encode, String.length_ofList, length_encodeList, ByteArray.length_toList]

/-- Decoding length, lifted to `ByteArray`/`String`. -/
theorem length_of_decode? {s : String} {data : ByteArray}
    (h : decode? s = some data) : s.length = 8 * ((data.size + 4) / 5) := by
  rw [← encode_decode? h, length_encode]

end Length

end Hex

end Rfc4648.Base32
