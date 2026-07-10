import Rfc4648.Util

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

/-! ## Round-trip and canonicity

Same statements as `Rfc4648.Base16`: strict decoding inverts encoding, and
the decoder accepts exactly the canonical encodings. -/

section RoundTrip

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

/-! Bounds on the 6-bit pieces produced by the encoder (`decide`, ≤ 256
cases each via `uint8_all`). -/

private theorem shr2_lt64 : ∀ b : UInt8, (b >>> 2).toNat < 64 :=
  uint8_all (by decide)

private theorem shr4_lt16 : ∀ b : UInt8, (b >>> 4).toNat < 16 :=
  uint8_all (by decide)

private theorem shr4_lt64 : ∀ b : UInt8, (b >>> 4).toNat < 64 :=
  uint8_all (by decide)

private theorem shr6_lt4 : ∀ b : UInt8, (b >>> 6).toNat < 4 :=
  uint8_all (by decide)

private theorem shr6_lt64 : ∀ b : UInt8, (b >>> 6).toNat < 64 :=
  uint8_all (by decide)

private theorem and3_lt4 : ∀ b : UInt8, (b &&& 0x03).toNat < 4 :=
  uint8_all (by decide)

private theorem and3_shl4_lt64 : ∀ b : UInt8, ((b &&& 0x03) <<< 4).toNat < 64 :=
  uint8_all (by decide)

private theorem and15_lt16 : ∀ b : UInt8, (b &&& 0x0F).toNat < 16 :=
  uint8_all (by decide)

private theorem and15_lt64 : ∀ b : UInt8, (b &&& 0x0F).toNat < 64 :=
  uint8_all (by decide)

private theorem and15_shl2_lt64 : ∀ b : UInt8, ((b &&& 0x0F) <<< 2).toNat < 64 :=
  uint8_all (by decide)

private theorem and63_lt64 : ∀ b : UInt8, (b &&& 0x3F).toNat < 64 :=
  uint8_all (by decide)

private theorem or_lt64 : ∀ x y : UInt8, x.toNat < 64 → y.toNat < 64 →
    (x ||| y).toNat < 64 :=
  uint8_all_lt₂ (by decide)

/-! Bounds on pieces of decoded 6-bit values. -/

private theorem shr4_lt4_of_lt64 : ∀ v : UInt8, v.toNat < 64 → (v >>> 4).toNat < 4 :=
  uint8_all (by decide)

private theorem shr2_lt16_of_lt64 : ∀ v : UInt8, v.toNat < 64 → (v >>> 2).toNat < 16 :=
  uint8_all (by decide)

/-! Splitting a byte and reassembling it (`decide`, 256 cases each). -/

private theorem recombine2 : ∀ b : UInt8, ((b >>> 2) <<< 2) ||| (b &&& 0x03) = b :=
  uint8_all (by decide)

private theorem recombine4 : ∀ b : UInt8, ((b >>> 4) <<< 4) ||| (b &&& 0x0F) = b :=
  uint8_all (by decide)

private theorem recombine6 : ∀ b : UInt8, ((b >>> 6) <<< 6) ||| (b &&& 0x3F) = b :=
  uint8_all (by decide)

private theorem unshift4_and3 : ∀ b : UInt8, ((b &&& 0x03) <<< 4) >>> 4 = b &&& 0x03 :=
  uint8_all (by decide)

private theorem unshift2_and15 : ∀ b : UInt8, ((b &&& 0x0F) <<< 2) >>> 2 = b &&& 0x0F :=
  uint8_all (by decide)

/-! The pad bits of a final partial group are zero. -/

private theorem pad_bits4 : ∀ b : UInt8, ((b &&& 0x03) <<< 4) &&& 0x0F = 0 :=
  uint8_all (by decide)

private theorem pad_bits2 : ∀ b : UInt8, ((b &&& 0x0F) <<< 2) &&& 0x03 = 0 :=
  uint8_all (by decide)

/-! Zero pad bits can be shifted out and back. -/

private theorem pad4_cancel : ∀ v : UInt8, v.toNat < 64 → v &&& 0x0F = 0 →
    (v >>> 4) <<< 4 = v :=
  uint8_all (by decide)

private theorem pad2_cancel : ∀ v : UInt8, v.toNat < 64 → v &&& 0x03 = 0 →
    (v >>> 2) <<< 2 = v :=
  uint8_all (by decide)

/-! Extracting one summand from a disjoint `|||` (`decide`, ≤ 4096 bounded
cases each via `uint8_all_lt₂`). -/

private theorem or_shr4 : ∀ x y : UInt8, x.toNat < 4 → y.toNat < 16 →
    ((x <<< 4) ||| y) >>> 4 = x :=
  uint8_all_lt₂ (by decide)

private theorem or_shl4 : ∀ x y : UInt8, x.toNat < 4 → y.toNat < 16 →
    ((x <<< 4) ||| y) <<< 4 = y <<< 4 :=
  uint8_all_lt₂ (by decide)

private theorem or_shr2 : ∀ x y : UInt8, x.toNat < 64 → y.toNat < 4 →
    ((x <<< 2) ||| y) >>> 2 = x :=
  uint8_all_lt₂ (by decide)

private theorem or_and3 : ∀ x y : UInt8, x.toNat < 64 → y.toNat < 4 →
    ((x <<< 2) ||| y) &&& 0x03 = y :=
  uint8_all_lt₂ (by decide)

private theorem or_shl6 : ∀ x y : UInt8, x.toNat < 16 → y.toNat < 4 →
    ((x <<< 2) ||| y) <<< 6 = y <<< 6 :=
  uint8_all_lt₂ (by decide)

private theorem or_shr4_and15 : ∀ x y : UInt8, x.toNat < 64 → y.toNat < 16 →
    ((x <<< 4) ||| y) >>> 4 = x &&& 0x0F :=
  uint8_all_lt₂ (by decide)

private theorem or_and15 : ∀ x y : UInt8, x.toNat < 64 → y.toNat < 16 →
    ((x <<< 4) ||| y) &&& 0x0F = y :=
  uint8_all_lt₂ (by decide)

private theorem or_shr6_and3 : ∀ x y : UInt8, x.toNat < 64 → y.toNat < 64 →
    ((x <<< 6) ||| y) >>> 6 = x &&& 0x03 :=
  uint8_all_lt₂ (by decide)

private theorem or_and63 : ∀ x y : UInt8, x.toNat < 64 → y.toNat < 64 →
    ((x <<< 6) ||| y) &&& 0x3F = y :=
  uint8_all_lt₂ (by decide)

/-! Character-map lemmas. -/

/-- `ofChar?` is a left inverse of `toChar` on 6-bit values. -/
theorem ofChar?_toChar : ∀ v : UInt8, v.toNat < 64 → ofChar? (toChar v) = some v :=
  uint8_all (by decide)

private theorem toChar_ne_pad : ∀ v : UInt8, v.toNat < 64 → toChar v ≠ '=' :=
  uint8_all (by decide)

/-- Characters accepted by `ofChar?` decode to 6-bit values, and `toChar`
maps those values back to the same character. -/
theorem ofChar?_eq_some {c : Char} {v : UInt8} (h : ofChar? c = some v) :
    v.toNat < 64 ∧ toChar v = c := by
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
    case isTrue haz =>
      obtain ⟨ha, hz⟩ := haz
      have ha' : 97 ≤ c.toNat := ha
      have hz' : c.toNat ≤ 122 := hz
      injection h with hv
      subst hv
      have ea : 'a'.toNat = 97 := rfl
      have hle : UInt8.ofNat 97 ≤ UInt8.ofNat c.toNat := by
        rw [UInt8.le_iff_toNat_le, UInt8.toNat_ofNat', UInt8.toNat_ofNat']
        omega
      have hval : (c.toNat.toUInt8 - 'a'.toNat.toUInt8 + 26).toNat = c.toNat - 71 := by
        simp only [Nat.toUInt8_eq, ea, UInt8.toNat_add, UInt8.toNat_sub_of_le _ _ hle,
          UInt8.toNat_ofNat', UInt8.toNat_ofNat]
        omega
      refine ⟨by omega, ?_⟩
      unfold toChar
      rw [if_neg (show ¬(_ < (26 : UInt8)) by
        rw [UInt8.lt_iff_toNat_lt, hval]; show ¬(c.toNat - 71 < 26); omega)]
      rw [if_pos (show _ < (52 : UInt8) by
        rw [UInt8.lt_iff_toNat_lt, hval]; show c.toNat - 71 < 52; omega)]
      rw [hval, show 'a'.toNat + (c.toNat - 71 - 26) = c.toNat by
        show 97 + (c.toNat - 71 - 26) = c.toNat; omega]
      exact Char.ofNat_toNat c
    case isFalse =>
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
        have hval : (c.toNat.toUInt8 - '0'.toNat.toUInt8 + 52).toNat = c.toNat + 4 := by
          simp only [Nat.toUInt8_eq, e0, UInt8.toNat_add, UInt8.toNat_sub_of_le _ _ hle,
            UInt8.toNat_ofNat', UInt8.toNat_ofNat]
          omega
        refine ⟨by omega, ?_⟩
        unfold toChar
        rw [if_neg (show ¬(_ < (26 : UInt8)) by
          rw [UInt8.lt_iff_toNat_lt, hval]; show ¬(c.toNat + 4 < 26); omega)]
        rw [if_neg (show ¬(_ < (52 : UInt8)) by
          rw [UInt8.lt_iff_toNat_lt, hval]; show ¬(c.toNat + 4 < 52); omega)]
        rw [if_pos (show _ < (62 : UInt8) by
          rw [UInt8.lt_iff_toNat_lt, hval]; show c.toNat + 4 < 62; omega)]
        rw [hval, show '0'.toNat + (c.toNat + 4 - 52) = c.toNat by
          show 48 + (c.toNat + 4 - 52) = c.toNat; omega]
        exact Char.ofNat_toNat c
      case isFalse =>
        split at h
        case isTrue hplus =>
          injection h with hv
          subst hv
          subst hplus
          exact ⟨by decide, by decide⟩
        case isFalse =>
          split at h
          case isTrue hslash =>
            injection h with hv
            subst hv
            subst hslash
            exact ⟨by decide, by decide⟩
          case isFalse => simp at h

/-! Main theorems. -/

/-- Round-trip: strictly decoding an encoding yields the original bytes. -/
theorem decodeList_encodeList : ∀ bs : List UInt8,
    decodeList (encodeList bs) = some bs
  | [] => rfl
  | [b0] => by
    simp only [encodeList, decodeList,
      ofChar?_toChar _ (shr2_lt64 b0), ofChar?_toChar _ (and3_shl4_lt64 b0),
      Option.bind_eq_bind, Option.bind_some]
    rw [if_pos trivial, if_pos ⟨trivial, trivial, pad_bits4 b0⟩,
      unshift4_and3 b0, recombine2 b0]
  | [b0, b1] => by
    have h1 : (((b0 &&& 0x03) <<< 4) ||| (b1 >>> 4)).toNat < 64 :=
      or_lt64 _ _ (and3_shl4_lt64 b0) (shr4_lt64 b1)
    simp only [encodeList, decodeList,
      ofChar?_toChar _ (shr2_lt64 b0), ofChar?_toChar _ h1,
      ofChar?_toChar _ (and15_shl2_lt64 b1),
      Option.bind_eq_bind, Option.bind_some]
    rw [if_neg (toChar_ne_pad _ (and15_shl2_lt64 b1)),
      if_pos trivial, if_pos ⟨trivial, pad_bits2 b1⟩,
      or_shr4 _ _ (and3_lt4 b0) (shr4_lt16 b1), recombine2 b0,
      or_shl4 _ _ (and3_lt4 b0) (shr4_lt16 b1),
      unshift2_and15 b1, recombine4 b1]
  | b0 :: b1 :: b2 :: rest => by
    have h1 : (((b0 &&& 0x03) <<< 4) ||| (b1 >>> 4)).toNat < 64 :=
      or_lt64 _ _ (and3_shl4_lt64 b0) (shr4_lt64 b1)
    have h2 : (((b1 &&& 0x0F) <<< 2) ||| (b2 >>> 6)).toNat < 64 :=
      or_lt64 _ _ (and15_shl2_lt64 b1) (shr6_lt64 b2)
    simp only [encodeList, decodeList,
      ofChar?_toChar _ (shr2_lt64 b0), ofChar?_toChar _ h1,
      ofChar?_toChar _ h2, ofChar?_toChar _ (and63_lt64 b2),
      Option.bind_eq_bind, Option.bind_some,
      decodeList_encodeList rest]
    rw [if_neg (toChar_ne_pad _ h2), if_neg (toChar_ne_pad _ (and63_lt64 b2)),
      or_shr4 _ _ (and3_lt4 b0) (shr4_lt16 b1), recombine2 b0,
      or_shl4 _ _ (and3_lt4 b0) (shr4_lt16 b1),
      or_shr2 _ _ (and15_lt64 b1) (shr6_lt4 b2), recombine4 b1,
      or_shl6 _ _ (and15_lt16 b1) (shr6_lt4 b2), recombine6 b2]

/-- Canonicity: every string the strict decoder accepts is the encoding of
the bytes it returns. -/
theorem encodeList_decodeList : ∀ {cs : List Char} {bs : List UInt8},
    decodeList cs = some bs → encodeList bs = cs
  | [], _, h => by
    simp only [decodeList, Option.some.injEq] at h
    simp [← h, encodeList]
  | _c0 :: _c1 :: c2 :: c3 :: rest, bs, h => by
    simp only [decodeList, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨v0, hv0, v1, hv1, h⟩ := h
    obtain ⟨hlt0, hc0⟩ := ofChar?_eq_some hv0
    obtain ⟨hlt1, hc1⟩ := ofChar?_eq_some hv1
    split at h
    case isTrue hc2 =>
      split at h
      case isTrue hcond =>
        obtain ⟨hc3, hrest, hpad⟩ := hcond
        injection h with h
        subst h
        subst hc2 hc3 hrest
        simp only [encodeList]
        rw [or_shr2 v0 (v1 >>> 4) hlt0 (shr4_lt4_of_lt64 v1 hlt1),
          or_and3 v0 (v1 >>> 4) hlt0 (shr4_lt4_of_lt64 v1 hlt1),
          pad4_cancel v1 hlt1 hpad, hc0, hc1]
      case isFalse => simp at h
    case isFalse hc2 =>
      simp only [Option.bind_eq_some_iff] at h
      obtain ⟨v2, hv2, h⟩ := h
      obtain ⟨hlt2, hc2'⟩ := ofChar?_eq_some hv2
      split at h
      case isTrue hc3 =>
        split at h
        case isTrue hcond =>
          obtain ⟨hrest, hpad⟩ := hcond
          injection h with h
          subst h
          subst hc3 hrest
          simp only [encodeList]
          rw [or_shr2 v0 (v1 >>> 4) hlt0 (shr4_lt4_of_lt64 v1 hlt1),
            or_and3 v0 (v1 >>> 4) hlt0 (shr4_lt4_of_lt64 v1 hlt1),
            or_shr4_and15 v1 (v2 >>> 2) hlt1 (shr2_lt16_of_lt64 v2 hlt2),
            recombine4 v1,
            or_and15 v1 (v2 >>> 2) hlt1 (shr2_lt16_of_lt64 v2 hlt2),
            pad2_cancel v2 hlt2 hpad, hc0, hc1, hc2']
        case isFalse => simp at h
      case isFalse hc3 =>
        simp only [Option.bind_eq_some_iff, Option.some.injEq] at h
        obtain ⟨v3, hv3, tail, htail, hbs⟩ := h
        obtain ⟨hlt3, hc3'⟩ := ofChar?_eq_some hv3
        subst hbs
        simp only [encodeList]
        rw [or_shr2 v0 (v1 >>> 4) hlt0 (shr4_lt4_of_lt64 v1 hlt1),
          or_and3 v0 (v1 >>> 4) hlt0 (shr4_lt4_of_lt64 v1 hlt1),
          or_shr4_and15 v1 (v2 >>> 2) hlt1 (shr2_lt16_of_lt64 v2 hlt2),
          recombine4 v1,
          or_and15 v1 (v2 >>> 2) hlt1 (shr2_lt16_of_lt64 v2 hlt2),
          or_shr6_and3 v2 v3 hlt2 hlt3, recombine2 v2,
          or_and63 v2 v3 hlt2 hlt3,
          encodeList_decodeList htail, hc0, hc1, hc2', hc3']
  | [_], _, h => by simp [decodeList] at h
  | [_, _], _, h => by simp [decodeList] at h
  | [_, _, _], _, h => by simp [decodeList] at h

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

end Rfc4648.Base64
