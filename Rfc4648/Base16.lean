import Rfc4648.Util

/-!
# RFC 4648 §8 — Base 16 Encoding

Encoder and strict decoder for base16 (hexadecimal).

Base16 is the degenerate case of the RFC 4648 family: each byte maps to
exactly two characters (4 bits each), so no padding is ever involved.

The decoder is strict: it accepts exactly the outputs of the encoder
(uppercase digits only, even length), per the RFC 4648 §12 security
considerations on canonical encodings.
-/

namespace Rfc4648.Base16

/-- Map a 4-bit value (`0`–`15`) to its character in the base16 alphabet
(RFC 4648 Table 5): `0`–`9`, `A`–`F`. -/
def toChar (v : UInt8) : Char :=
  if v < 10 then Char.ofNat ('0'.toNat + v.toNat)
  else Char.ofNat ('A'.toNat + (v.toNat - 10))

/-- Map a character to its 4-bit value, or `none` if it is not in the
base16 alphabet. Inverse of `toChar`. Lowercase is rejected: only the
canonical uppercase alphabet decodes. -/
def ofChar? (c : Char) : Option UInt8 :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat.toUInt8 - '0'.toNat.toUInt8)
  else if 'A' ≤ c ∧ c ≤ 'F' then some (c.toNat.toUInt8 - 'A'.toNat.toUInt8 + 10)
  else none

/-- Encode bytes as base16 characters: each byte becomes two characters,
high nibble first (RFC 4648 §8). -/
def encodeList : List UInt8 → List Char
  | [] => []
  | b :: rest => toChar (b >>> 4) :: toChar (b &&& 0x0F) :: encodeList rest

/-- Strictly decode base16 characters, one character pair per byte.
Returns `none` if the length is odd or any character is outside the
uppercase base16 alphabet. -/
def decodeList : List Char → Option (List UInt8)
  | [] => some []
  | c0 :: c1 :: rest => do
    let v0 ← ofChar? c0
    let v1 ← ofChar? c1
    let tail ← decodeList rest
    some (((v0 <<< 4) ||| v1) :: tail)
  | _ => none

/-- Encode a byte array as a base16 (hex) string (RFC 4648 §8). -/
def encode (data : ByteArray) : String :=
  String.ofList (encodeList data.toList)

/-- Strictly decode a base16 string. Returns `none` if the input is not a
canonical RFC 4648 §8 encoding. -/
def decode? (s : String) : Option ByteArray :=
  (decodeList s.toList).map fun bytes => ByteArray.mk bytes.toArray

/-! ## Test vectors (RFC 4648 §10), checked at compile time -/

#guard encode "".toUTF8 = ""
#guard encode "f".toUTF8 = "66"
#guard encode "fo".toUTF8 = "666F"
#guard encode "foo".toUTF8 = "666F6F"
#guard encode "foob".toUTF8 = "666F6F62"
#guard encode "fooba".toUTF8 = "666F6F6261"
#guard encode "foobar".toUTF8 = "666F6F626172"

#guard (decode? "").map ByteArray.toList = some "".toUTF8.toList
#guard (decode? "66").map ByteArray.toList = some "f".toUTF8.toList
#guard (decode? "666F").map ByteArray.toList = some "fo".toUTF8.toList
#guard (decode? "666F6F").map ByteArray.toList = some "foo".toUTF8.toList
#guard (decode? "666F6F62").map ByteArray.toList = some "foob".toUTF8.toList
#guard (decode? "666F6F6261").map ByteArray.toList = some "fooba".toUTF8.toList
#guard (decode? "666F6F626172").map ByteArray.toList = some "foobar".toUTF8.toList

/-! Strictness: malformed inputs are rejected. -/

#guard (decode? "6").isNone       -- odd length
#guard (decode? "666f").isNone    -- lowercase is not canonical
#guard (decode? "6G").isNone      -- character outside the alphabet
#guard (decode? "66=").isNone     -- base16 has no padding

/-! ## Round-trip and canonicity

`decodeList_encodeList` / `decode?_encode`: decoding an encoding gives back
the input. `encodeList_decodeList` / `encode_decode?`: anything the strict
decoder accepts is the encoding of its output, i.e. the decoder accepts
exactly the canonical encodings. -/

section RoundTrip

set_option maxRecDepth 4096

private theorem hi_lt : ∀ b : UInt8, b >>> 4 < 16 :=
  uint8_all (by decide)

private theorem lo_lt : ∀ b : UInt8, b &&& 0x0F < 16 :=
  uint8_all (by decide)

private theorem hi_lo_recombine : ∀ b : UInt8,
    ((b >>> 4) <<< 4) ||| (b &&& 0x0F) = b :=
  uint8_all (by decide)

/-- `ofChar?` is a left inverse of `toChar` on 4-bit values. -/
theorem ofChar?_toChar : ∀ v : UInt8, v < 16 → ofChar? (toChar v) = some v :=
  uint8_all (by decide)

private theorem or_hi : ∀ x y : UInt8, x.toNat < 16 → y.toNat < 16 →
    ((x <<< 4) ||| y) >>> 4 = x :=
  uint8_all_lt₂ (by decide)

private theorem or_lo : ∀ x y : UInt8, x.toNat < 16 → y.toNat < 16 →
    ((x <<< 4) ||| y) &&& 0x0F = y :=
  uint8_all_lt₂ (by decide)

/-- Characters accepted by `ofChar?` decode to 4-bit values, and `toChar`
maps those values back to the same character. -/
theorem ofChar?_eq_some {c : Char} {v : UInt8} (h : ofChar? c = some v) :
    v.toNat < 16 ∧ toChar v = c := by
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
    case isTrue hAF =>
      obtain ⟨hA, hF⟩ := hAF
      have hA' : 65 ≤ c.toNat := hA
      have hF' : c.toNat ≤ 70 := hF
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
  | b :: rest => by
    simp only [encodeList, decodeList, ofChar?_toChar _ (hi_lt b),
      ofChar?_toChar _ (lo_lt b), Option.bind_eq_bind, Option.bind_some,
      decodeList_encodeList rest, hi_lo_recombine b]

/-- Canonicity: every string the strict decoder accepts is the encoding of
the bytes it returns. -/
theorem encodeList_decodeList : ∀ {cs : List Char} {bs : List UInt8},
    decodeList cs = some bs → encodeList bs = cs
  | [], _, h => by
    simp only [decodeList, Option.some.injEq] at h
    simp [← h, encodeList]
  | _c0 :: _c1 :: rest, bs, h => by
    simp only [decodeList, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.some.injEq] at h
    obtain ⟨v0, hv0, v1, hv1, tail, htail, hbs⟩ := h
    obtain ⟨hlt0, hc0⟩ := ofChar?_eq_some hv0
    obtain ⟨hlt1, hc1⟩ := ofChar?_eq_some hv1
    subst hbs
    simp only [encodeList, or_hi v0 v1 hlt0 hlt1, or_lo v0 v1 hlt0 hlt1,
      hc0, hc1, encodeList_decodeList htail]
  | [_], _, h => by simp [decodeList] at h

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

end Rfc4648.Base16
