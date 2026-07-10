import Std.Tactic.BVDecide
import Rfc4648.Util
import Rfc4648.Alphabet

/-!
# RFC 4648 §6 / §7 — Base 32 Encodings

Encoder and strict decoder for base32, parameterized over an
`Alphabet 32`. Two alphabets are provided: `Base32.alphabet` (§6,
`A`–`Z` `2`–`7`) and `Base32.Hex.alphabet` (§7, `0`–`9` `A`–`V`, the
extended-hex alphabet whose encodings sort like the underlying bytes).
The codec and all its theorems are proved once, generically.

Base32 processes 40-bit groups: 5 bytes become 8 characters of 5 bits
each. A final group of 1, 2, 3, or 4 bytes is zero-padded to a whole
number of 5-bit values and the output filled to 8 characters with
6, 4, 3, or 1 `=` respectively.

The decoder is strict (RFC 4648 §3.5, §12): it accepts exactly the
outputs of the encoder.
-/

namespace Rfc4648.Base32

/-! ## The §6 alphabet -/

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

section CharLemmas

set_option maxRecDepth 4096

theorem ofChar?_toChar : ∀ v : UInt8, v < 32 → ofChar? (toChar v) = some v :=
  uint8_all (by decide)

theorem toChar_ne_pad : ∀ v : UInt8, v < 32 → toChar v ≠ '=' :=
  uint8_all (by decide)

theorem ofChar?_eq_some {c : Char} {v : UInt8} (h : ofChar? c = some v) :
    v < 32 ∧ toChar v = c := by
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
    refine ⟨by rw [UInt8.lt_iff_toNat_lt, hval]; show c.toNat - 65 < 32; omega, ?_⟩
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
      refine ⟨by rw [UInt8.lt_iff_toNat_lt, hval]; show c.toNat - 24 < 32; omega, ?_⟩
      unfold toChar
      rw [if_neg (show ¬(_ < (26 : UInt8)) by
        rw [UInt8.lt_iff_toNat_lt, hval]; show ¬(c.toNat - 24 < 26); omega)]
      rw [hval, show '2'.toNat + (c.toNat - 24 - 26) = c.toNat by
        show 50 + (c.toNat - 24 - 26) = c.toNat; omega]
      exact Char.ofNat_toNat c
    case isFalse => simp at h

end CharLemmas

/-- The base32 alphabet of RFC 4648 §6 (Table 3). -/
def alphabet : Alphabet 32 where
  toChar := toChar
  ofChar? := ofChar?
  ofChar?_toChar := ofChar?_toChar
  toChar_ne_pad := toChar_ne_pad
  ofChar?_eq_some := ofChar?_eq_some

/-! ## The codec, parameterized over the alphabet -/

/-- Encode bytes as base32 characters, processing one 40-bit group
(5 bytes → 8 characters) per step. A final group of 1–4 bytes is
zero-padded to a whole number of 5-bit values and the output filled to
8 characters with `=` (RFC 4648 §6). -/
def encodeList (α : Alphabet 32) : List UInt8 → List Char
  | [] => []
  | [b0] =>
    [α.toChar (b0 >>> 3),
     α.toChar ((b0 &&& 0x07) <<< 2),
     '=', '=', '=', '=', '=', '=']
  | [b0, b1] =>
    [α.toChar (b0 >>> 3),
     α.toChar (((b0 &&& 0x07) <<< 2) ||| (b1 >>> 6)),
     α.toChar ((b1 >>> 1) &&& 0x1F),
     α.toChar ((b1 &&& 0x01) <<< 4),
     '=', '=', '=', '=']
  | [b0, b1, b2] =>
    [α.toChar (b0 >>> 3),
     α.toChar (((b0 &&& 0x07) <<< 2) ||| (b1 >>> 6)),
     α.toChar ((b1 >>> 1) &&& 0x1F),
     α.toChar (((b1 &&& 0x01) <<< 4) ||| (b2 >>> 4)),
     α.toChar ((b2 &&& 0x0F) <<< 1),
     '=', '=', '=']
  | [b0, b1, b2, b3] =>
    [α.toChar (b0 >>> 3),
     α.toChar (((b0 &&& 0x07) <<< 2) ||| (b1 >>> 6)),
     α.toChar ((b1 >>> 1) &&& 0x1F),
     α.toChar (((b1 &&& 0x01) <<< 4) ||| (b2 >>> 4)),
     α.toChar (((b2 &&& 0x0F) <<< 1) ||| (b3 >>> 7)),
     α.toChar ((b3 >>> 2) &&& 0x1F),
     α.toChar ((b3 &&& 0x03) <<< 3),
     '=']
  | b0 :: b1 :: b2 :: b3 :: b4 :: rest =>
    α.toChar (b0 >>> 3) ::
    α.toChar (((b0 &&& 0x07) <<< 2) ||| (b1 >>> 6)) ::
    α.toChar ((b1 >>> 1) &&& 0x1F) ::
    α.toChar (((b1 &&& 0x01) <<< 4) ||| (b2 >>> 4)) ::
    α.toChar (((b2 &&& 0x0F) <<< 1) ||| (b3 >>> 7)) ::
    α.toChar ((b3 >>> 2) &&& 0x1F) ::
    α.toChar (((b3 &&& 0x03) <<< 3) ||| (b4 >>> 5)) ::
    α.toChar (b4 &&& 0x1F) ::
    encodeList α rest

/-- Strictly decode base32 characters, one 8-character group per step.
Returns `none` unless the input is a canonical encoding: length a multiple
of 8, padding (of a valid length: 1, 3, 4, or 6) only in the final group,
and all pad bits zero. -/
def decodeList (α : Alphabet 32) : List Char → Option (List UInt8)
  | [] => some []
  | c0 :: c1 :: c2 :: c3 :: c4 :: c5 :: c6 :: c7 :: rest => do
    let v0 ← α.ofChar? c0
    let v1 ← α.ofChar? c1
    if c2 = '=' then
      -- "xx======": one output byte; the low 2 bits of v1 are pad bits.
      if c3 = '=' ∧ c4 = '=' ∧ c5 = '=' ∧ c6 = '=' ∧ c7 = '=' ∧ rest = [] ∧
          v1 &&& 0x03 = 0 then
        some [(v0 <<< 3) ||| (v1 >>> 2)]
      else none
    else do
      let v2 ← α.ofChar? c2
      let v3 ← α.ofChar? c3
      if c4 = '=' then
        -- "xxxx====": two output bytes; the low 4 bits of v3 are pad bits.
        if c5 = '=' ∧ c6 = '=' ∧ c7 = '=' ∧ rest = [] ∧ v3 &&& 0x0F = 0 then
          some [(v0 <<< 3) ||| (v1 >>> 2),
                (v1 <<< 6) ||| (v2 <<< 1) ||| (v3 >>> 4)]
        else none
      else do
        let v4 ← α.ofChar? c4
        if c5 = '=' then
          -- "xxxxx===": three output bytes; the low bit of v4 is a pad bit.
          if c6 = '=' ∧ c7 = '=' ∧ rest = [] ∧ v4 &&& 0x01 = 0 then
            some [(v0 <<< 3) ||| (v1 >>> 2),
                  (v1 <<< 6) ||| (v2 <<< 1) ||| (v3 >>> 4),
                  (v3 <<< 4) ||| (v4 >>> 1)]
          else none
        else do
          let v5 ← α.ofChar? c5
          let v6 ← α.ofChar? c6
          if c7 = '=' then
            -- "xxxxxxx=": four output bytes; the low 3 bits of v6 are pad bits.
            if rest = [] ∧ v6 &&& 0x07 = 0 then
              some [(v0 <<< 3) ||| (v1 >>> 2),
                    (v1 <<< 6) ||| (v2 <<< 1) ||| (v3 >>> 4),
                    (v3 <<< 4) ||| (v4 >>> 1),
                    (v4 <<< 7) ||| (v5 <<< 2) ||| (v6 >>> 3)]
            else none
          else do
            let v7 ← α.ofChar? c7
            let tail ← decodeList α rest
            some (((v0 <<< 3) ||| (v1 >>> 2)) ::
                  ((v1 <<< 6) ||| (v2 <<< 1) ||| (v3 >>> 4)) ::
                  ((v3 <<< 4) ||| (v4 >>> 1)) ::
                  ((v4 <<< 7) ||| (v5 <<< 2) ||| (v6 >>> 3)) ::
                  ((v6 <<< 5) ||| v7) ::
                  tail)
  | _ => none

/-- Encode a byte array as a base32 string (RFC 4648 §6, with padding). -/
def encode (data : ByteArray) : String :=
  String.ofList (encodeList alphabet data.toList)

/-- Strictly decode a base32 string. Returns `none` if the input is not a
canonical RFC 4648 §6 encoding. -/
def decode? (s : String) : Option ByteArray :=
  (decodeList alphabet s.toList).map fun bytes => ByteArray.mk bytes.toArray

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

The list-level theorems hold for any `Alphabet 32`. -/

section RoundTrip

/-! Bounds on the 5-bit values produced by the encoder. -/

private theorem w0_lt (b0 : UInt8) : b0 >>> 3 < 32 := by bv_decide

private theorem w1_lt (b0 b1 : UInt8) :
    ((b0 &&& 0x07) <<< 2) ||| (b1 >>> 6) < 32 := by bv_decide

private theorem w1p_lt (b0 : UInt8) : (b0 &&& 0x07) <<< 2 < 32 := by bv_decide

private theorem w2_lt (b1 : UInt8) : (b1 >>> 1) &&& 0x1F < 32 := by bv_decide

private theorem w3_lt (b1 b2 : UInt8) :
    ((b1 &&& 0x01) <<< 4) ||| (b2 >>> 4) < 32 := by bv_decide

private theorem w3p_lt (b1 : UInt8) : (b1 &&& 0x01) <<< 4 < 32 := by bv_decide

private theorem w4_lt (b2 b3 : UInt8) :
    ((b2 &&& 0x0F) <<< 1) ||| (b3 >>> 7) < 32 := by bv_decide

private theorem w4p_lt (b2 : UInt8) : (b2 &&& 0x0F) <<< 1 < 32 := by bv_decide

private theorem w5_lt (b3 : UInt8) : (b3 >>> 2) &&& 0x1F < 32 := by bv_decide

private theorem w6_lt (b3 b4 : UInt8) :
    ((b3 &&& 0x03) <<< 3) ||| (b4 >>> 5) < 32 := by bv_decide

private theorem w6p_lt (b3 : UInt8) : (b3 &&& 0x03) <<< 3 < 32 := by bv_decide

private theorem w7_lt (b4 : UInt8) : b4 &&& 0x1F < 32 := by bv_decide

/-- Round-trip: strictly decoding an encoding yields the original bytes. -/
theorem decodeList_encodeList (α : Alphabet 32) : ∀ bs : List UInt8,
    decodeList α (encodeList α bs) = some bs
  | [] => rfl
  | [b0] => by
    simp only [encodeList, decodeList,
      α.ofChar?_toChar _ (w0_lt b0), α.ofChar?_toChar _ (w1p_lt b0),
      Option.bind_eq_bind, Option.bind_some]
    rw [if_pos trivial,
      if_pos ⟨trivial, trivial, trivial, trivial, trivial, trivial, by bv_decide⟩]
    have e0 : ((b0 >>> 3) <<< 3) ||| (((b0 &&& 0x07) <<< 2) >>> 2) = b0 := by
      bv_decide
    rw [e0]
  | [b0, b1] => by
    simp only [encodeList, decodeList,
      α.ofChar?_toChar _ (w0_lt b0), α.ofChar?_toChar _ (w1_lt b0 b1),
      α.ofChar?_toChar _ (w2_lt b1), α.ofChar?_toChar _ (w3p_lt b1),
      Option.bind_eq_bind, Option.bind_some]
    rw [if_neg (α.toChar_ne_pad _ (w2_lt b1)),
      if_pos trivial, if_pos ⟨trivial, trivial, trivial, trivial, by bv_decide⟩]
    have e0 : ((b0 >>> 3) <<< 3) |||
        ((((b0 &&& 0x07) <<< 2) ||| (b1 >>> 6)) >>> 2) = b0 := by bv_decide
    have e1 : ((((b0 &&& 0x07) <<< 2) ||| (b1 >>> 6)) <<< 6) |||
        (((b1 >>> 1) &&& 0x1F) <<< 1) ||| (((b1 &&& 0x01) <<< 4) >>> 4) = b1 := by
      bv_decide
    rw [e0, e1]
  | [b0, b1, b2] => by
    simp only [encodeList, decodeList,
      α.ofChar?_toChar _ (w0_lt b0), α.ofChar?_toChar _ (w1_lt b0 b1),
      α.ofChar?_toChar _ (w2_lt b1), α.ofChar?_toChar _ (w3_lt b1 b2),
      α.ofChar?_toChar _ (w4p_lt b2),
      Option.bind_eq_bind, Option.bind_some]
    rw [if_neg (α.toChar_ne_pad _ (w2_lt b1)),
      if_neg (α.toChar_ne_pad _ (w4p_lt b2)),
      if_pos trivial, if_pos ⟨trivial, trivial, trivial, by bv_decide⟩]
    have e0 : ((b0 >>> 3) <<< 3) |||
        ((((b0 &&& 0x07) <<< 2) ||| (b1 >>> 6)) >>> 2) = b0 := by bv_decide
    have e1 : ((((b0 &&& 0x07) <<< 2) ||| (b1 >>> 6)) <<< 6) |||
        (((b1 >>> 1) &&& 0x1F) <<< 1) |||
        ((((b1 &&& 0x01) <<< 4) ||| (b2 >>> 4)) >>> 4) = b1 := by bv_decide
    have e2 : ((((b1 &&& 0x01) <<< 4) ||| (b2 >>> 4)) <<< 4) |||
        (((b2 &&& 0x0F) <<< 1) >>> 1) = b2 := by bv_decide
    rw [e0, e1, e2]
  | [b0, b1, b2, b3] => by
    simp only [encodeList, decodeList,
      α.ofChar?_toChar _ (w0_lt b0), α.ofChar?_toChar _ (w1_lt b0 b1),
      α.ofChar?_toChar _ (w2_lt b1), α.ofChar?_toChar _ (w3_lt b1 b2),
      α.ofChar?_toChar _ (w4_lt b2 b3), α.ofChar?_toChar _ (w5_lt b3),
      α.ofChar?_toChar _ (w6p_lt b3),
      Option.bind_eq_bind, Option.bind_some]
    rw [if_neg (α.toChar_ne_pad _ (w2_lt b1)),
      if_neg (α.toChar_ne_pad _ (w4_lt b2 b3)),
      if_neg (α.toChar_ne_pad _ (w5_lt b3)),
      if_pos trivial, if_pos ⟨trivial, by bv_decide⟩]
    have e0 : ((b0 >>> 3) <<< 3) |||
        ((((b0 &&& 0x07) <<< 2) ||| (b1 >>> 6)) >>> 2) = b0 := by bv_decide
    have e1 : ((((b0 &&& 0x07) <<< 2) ||| (b1 >>> 6)) <<< 6) |||
        (((b1 >>> 1) &&& 0x1F) <<< 1) |||
        ((((b1 &&& 0x01) <<< 4) ||| (b2 >>> 4)) >>> 4) = b1 := by bv_decide
    have e2 : ((((b1 &&& 0x01) <<< 4) ||| (b2 >>> 4)) <<< 4) |||
        ((((b2 &&& 0x0F) <<< 1) ||| (b3 >>> 7)) >>> 1) = b2 := by bv_decide
    have e3 : ((((b2 &&& 0x0F) <<< 1) ||| (b3 >>> 7)) <<< 7) |||
        (((b3 >>> 2) &&& 0x1F) <<< 2) ||| (((b3 &&& 0x03) <<< 3) >>> 3) = b3 := by
      bv_decide
    rw [e0, e1, e2, e3]
  | b0 :: b1 :: b2 :: b3 :: b4 :: rest => by
    simp only [encodeList, decodeList,
      α.ofChar?_toChar _ (w0_lt b0), α.ofChar?_toChar _ (w1_lt b0 b1),
      α.ofChar?_toChar _ (w2_lt b1), α.ofChar?_toChar _ (w3_lt b1 b2),
      α.ofChar?_toChar _ (w4_lt b2 b3), α.ofChar?_toChar _ (w5_lt b3),
      α.ofChar?_toChar _ (w6_lt b3 b4), α.ofChar?_toChar _ (w7_lt b4),
      Option.bind_eq_bind, Option.bind_some,
      decodeList_encodeList α rest]
    rw [if_neg (α.toChar_ne_pad _ (w2_lt b1)),
      if_neg (α.toChar_ne_pad _ (w4_lt b2 b3)),
      if_neg (α.toChar_ne_pad _ (w5_lt b3)),
      if_neg (α.toChar_ne_pad _ (w7_lt b4))]
    have e0 : ((b0 >>> 3) <<< 3) |||
        ((((b0 &&& 0x07) <<< 2) ||| (b1 >>> 6)) >>> 2) = b0 := by bv_decide
    have e1 : ((((b0 &&& 0x07) <<< 2) ||| (b1 >>> 6)) <<< 6) |||
        (((b1 >>> 1) &&& 0x1F) <<< 1) |||
        ((((b1 &&& 0x01) <<< 4) ||| (b2 >>> 4)) >>> 4) = b1 := by bv_decide
    have e2 : ((((b1 &&& 0x01) <<< 4) ||| (b2 >>> 4)) <<< 4) |||
        ((((b2 &&& 0x0F) <<< 1) ||| (b3 >>> 7)) >>> 1) = b2 := by bv_decide
    have e3 : ((((b2 &&& 0x0F) <<< 1) ||| (b3 >>> 7)) <<< 7) |||
        (((b3 >>> 2) &&& 0x1F) <<< 2) |||
        ((((b3 &&& 0x03) <<< 3) ||| (b4 >>> 5)) >>> 3) = b3 := by bv_decide
    have e4 : ((((b3 &&& 0x03) <<< 3) ||| (b4 >>> 5)) <<< 5) |||
        (b4 &&& 0x1F) = b4 := by bv_decide
    rw [e0, e1, e2, e3, e4]

/-- Canonicity: every string the strict decoder accepts is the encoding of
the bytes it returns. -/
theorem encodeList_decodeList (α : Alphabet 32) : ∀ {cs : List Char} {bs : List UInt8},
    decodeList α cs = some bs → encodeList α bs = cs
  | [], _, h => by
    simp only [decodeList, Option.some.injEq] at h
    simp [← h, encodeList]
  | _c0 :: _c1 :: c2 :: c3 :: c4 :: c5 :: c6 :: c7 :: rest, bs, h => by
    simp only [decodeList, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨v0, hv0, v1, hv1, h⟩ := h
    obtain ⟨hlt0, hc0⟩ := α.ofChar?_eq_some hv0
    obtain ⟨hlt1, hc1⟩ := α.ofChar?_eq_some hv1
    split at h
    case isTrue hc2 =>
      split at h
      case isTrue hcond =>
        obtain ⟨hc3, hc4, hc5, hc6, hc7, hrest, hpad⟩ := hcond
        injection h with h
        subst h
        subst hc2 hc3 hc4 hc5 hc6 hc7 hrest
        have e0 : ((v0 <<< 3) ||| (v1 >>> 2)) >>> 3 = v0 := by bv_decide
        have e1 : (((v0 <<< 3) ||| (v1 >>> 2)) &&& 0x07) <<< 2 = v1 := by bv_decide
        simp only [encodeList]
        rw [e0, e1, hc0, hc1]
      case isFalse => simp at h
    case isFalse hc2 =>
      simp only [Option.bind_eq_some_iff] at h
      obtain ⟨v2, hv2, v3, hv3, h⟩ := h
      obtain ⟨hlt2, hc2'⟩ := α.ofChar?_eq_some hv2
      obtain ⟨hlt3, hc3'⟩ := α.ofChar?_eq_some hv3
      split at h
      case isTrue hc4 =>
        split at h
        case isTrue hcond =>
          obtain ⟨hc5, hc6, hc7, hrest, hpad⟩ := hcond
          injection h with h
          subst h
          subst hc4 hc5 hc6 hc7 hrest
          have e0 : ((v0 <<< 3) ||| (v1 >>> 2)) >>> 3 = v0 := by bv_decide
          have e1 : ((((v0 <<< 3) ||| (v1 >>> 2)) &&& 0x07) <<< 2) |||
              (((v1 <<< 6) ||| (v2 <<< 1) ||| (v3 >>> 4)) >>> 6) = v1 := by bv_decide
          have e2 : (((v1 <<< 6) ||| (v2 <<< 1) ||| (v3 >>> 4)) >>> 1) &&& 0x1F = v2 := by
            bv_decide
          have e3 : (((v1 <<< 6) ||| (v2 <<< 1) ||| (v3 >>> 4)) &&& 0x01) <<< 4 = v3 := by
            bv_decide
          simp only [encodeList]
          rw [e0, e1, e2, e3, hc0, hc1, hc2', hc3']
        case isFalse => simp at h
      case isFalse hc4 =>
        simp only [Option.bind_eq_some_iff] at h
        obtain ⟨v4, hv4, h⟩ := h
        obtain ⟨hlt4, hc4'⟩ := α.ofChar?_eq_some hv4
        split at h
        case isTrue hc5 =>
          split at h
          case isTrue hcond =>
            obtain ⟨hc6, hc7, hrest, hpad⟩ := hcond
            injection h with h
            subst h
            subst hc5 hc6 hc7 hrest
            have e0 : ((v0 <<< 3) ||| (v1 >>> 2)) >>> 3 = v0 := by bv_decide
            have e1 : ((((v0 <<< 3) ||| (v1 >>> 2)) &&& 0x07) <<< 2) |||
                (((v1 <<< 6) ||| (v2 <<< 1) ||| (v3 >>> 4)) >>> 6) = v1 := by bv_decide
            have e2 : (((v1 <<< 6) ||| (v2 <<< 1) ||| (v3 >>> 4)) >>> 1) &&& 0x1F = v2 := by
              bv_decide
            have e3 : ((((v1 <<< 6) ||| (v2 <<< 1) ||| (v3 >>> 4)) &&& 0x01) <<< 4) |||
                (((v3 <<< 4) ||| (v4 >>> 1)) >>> 4) = v3 := by bv_decide
            have e4 : (((v3 <<< 4) ||| (v4 >>> 1)) &&& 0x0F) <<< 1 = v4 := by bv_decide
            simp only [encodeList]
            rw [e0, e1, e2, e3, e4, hc0, hc1, hc2', hc3', hc4']
          case isFalse => simp at h
        case isFalse hc5 =>
          simp only [Option.bind_eq_some_iff] at h
          obtain ⟨v5, hv5, v6, hv6, h⟩ := h
          obtain ⟨hlt5, hc5'⟩ := α.ofChar?_eq_some hv5
          obtain ⟨hlt6, hc6'⟩ := α.ofChar?_eq_some hv6
          split at h
          case isTrue hc7 =>
            split at h
            case isTrue hcond =>
              obtain ⟨hrest, hpad⟩ := hcond
              injection h with h
              subst h
              subst hc7 hrest
              have e0 : ((v0 <<< 3) ||| (v1 >>> 2)) >>> 3 = v0 := by bv_decide
              have e1 : ((((v0 <<< 3) ||| (v1 >>> 2)) &&& 0x07) <<< 2) |||
                  (((v1 <<< 6) ||| (v2 <<< 1) ||| (v3 >>> 4)) >>> 6) = v1 := by bv_decide
              have e2 : (((v1 <<< 6) ||| (v2 <<< 1) ||| (v3 >>> 4)) >>> 1) &&& 0x1F = v2 := by
                bv_decide
              have e3 : ((((v1 <<< 6) ||| (v2 <<< 1) ||| (v3 >>> 4)) &&& 0x01) <<< 4) |||
                  (((v3 <<< 4) ||| (v4 >>> 1)) >>> 4) = v3 := by bv_decide
              have e4 : ((((v3 <<< 4) ||| (v4 >>> 1)) &&& 0x0F) <<< 1) |||
                  (((v4 <<< 7) ||| (v5 <<< 2) ||| (v6 >>> 3)) >>> 7) = v4 := by bv_decide
              have e5 : (((v4 <<< 7) ||| (v5 <<< 2) ||| (v6 >>> 3)) >>> 2) &&& 0x1F = v5 := by
                bv_decide
              have e6 : (((v4 <<< 7) ||| (v5 <<< 2) ||| (v6 >>> 3)) &&& 0x03) <<< 3 = v6 := by
                bv_decide
              simp only [encodeList]
              rw [e0, e1, e2, e3, e4, e5, e6, hc0, hc1, hc2', hc3', hc4', hc5', hc6']
            case isFalse => simp at h
          case isFalse hc7 =>
            simp only [Option.bind_eq_some_iff, Option.some.injEq] at h
            obtain ⟨v7, hv7, tail, htail, hbs⟩ := h
            obtain ⟨hlt7, hc7'⟩ := α.ofChar?_eq_some hv7
            subst hbs
            have e0 : ((v0 <<< 3) ||| (v1 >>> 2)) >>> 3 = v0 := by bv_decide
            have e1 : ((((v0 <<< 3) ||| (v1 >>> 2)) &&& 0x07) <<< 2) |||
                (((v1 <<< 6) ||| (v2 <<< 1) ||| (v3 >>> 4)) >>> 6) = v1 := by bv_decide
            have e2 : (((v1 <<< 6) ||| (v2 <<< 1) ||| (v3 >>> 4)) >>> 1) &&& 0x1F = v2 := by
              bv_decide
            have e3 : ((((v1 <<< 6) ||| (v2 <<< 1) ||| (v3 >>> 4)) &&& 0x01) <<< 4) |||
                (((v3 <<< 4) ||| (v4 >>> 1)) >>> 4) = v3 := by bv_decide
            have e4 : ((((v3 <<< 4) ||| (v4 >>> 1)) &&& 0x0F) <<< 1) |||
                (((v4 <<< 7) ||| (v5 <<< 2) ||| (v6 >>> 3)) >>> 7) = v4 := by bv_decide
            have e5 : (((v4 <<< 7) ||| (v5 <<< 2) ||| (v6 >>> 3)) >>> 2) &&& 0x1F = v5 := by
              bv_decide
            have e6 : ((((v4 <<< 7) ||| (v5 <<< 2) ||| (v6 >>> 3)) &&& 0x03) <<< 3) |||
                (((v6 <<< 5) ||| v7) >>> 5) = v6 := by bv_decide
            have e7 : ((v6 <<< 5) ||| v7) &&& 0x1F = v7 := by bv_decide
            simp only [encodeList]
            rw [e0, e1, e2, e3, e4, e5, e6, e7, encodeList_decodeList α htail,
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
  rw [encodeList_decodeList alphabet hl, String.ofList_toList]

end RoundTrip

/-! ## Output length -/

section Length

/-- The encoding of `n` bytes has exactly `8 * ((n + 4) / 5)` characters. -/
theorem length_encodeList (α : Alphabet 32) : ∀ bs : List UInt8,
    (encodeList α bs).length = 8 * ((bs.length + 4) / 5)
  | [] => rfl
  | [_] => by simp [encodeList]
  | [_, _] => by simp [encodeList]
  | [_, _, _] => by simp [encodeList]
  | [_, _, _, _] => by simp [encodeList]
  | b0 :: b1 :: b2 :: b3 :: b4 :: rest => by
    simp only [encodeList, List.length_cons, length_encodeList α rest]
    omega

/-- Anything the strict decoder accepts has the padded encoding length of
its output. -/
theorem length_of_decodeList {α : Alphabet 32} {cs : List Char} {bs : List UInt8}
    (h : decodeList α cs = some bs) : cs.length = 8 * ((bs.length + 4) / 5) := by
  rw [← encodeList_decodeList α h, length_encodeList]

/-- Anything the strict decoder accepts has length divisible by 8. -/
theorem length_of_decodeList_mod {α : Alphabet 32} {cs : List Char} {bs : List UInt8}
    (h : decodeList α cs = some bs) : cs.length % 8 = 0 := by
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

The same verified codec applied to the §7 alphabet: `0`–`9`, `A`–`V`,
chosen so that encoded data sorts in the same order as the underlying
bytes. -/

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

section CharLemmas

set_option maxRecDepth 4096

theorem ofChar?_toChar : ∀ v : UInt8, v < 32 → ofChar? (toChar v) = some v :=
  uint8_all (by decide)

theorem toChar_ne_pad : ∀ v : UInt8, v < 32 → toChar v ≠ '=' :=
  uint8_all (by decide)

theorem ofChar?_eq_some {c : Char} {v : UInt8} (h : ofChar? c = some v) :
    v < 32 ∧ toChar v = c := by
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
    refine ⟨by rw [UInt8.lt_iff_toNat_lt, hval]; show c.toNat - 48 < 32; omega, ?_⟩
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
      refine ⟨by rw [UInt8.lt_iff_toNat_lt, hval]; show c.toNat - 55 < 32; omega, ?_⟩
      unfold toChar
      rw [if_neg (show ¬(_ < (10 : UInt8)) by
        rw [UInt8.lt_iff_toNat_lt, hval]; show ¬(c.toNat - 55 < 10); omega)]
      rw [hval, show 'A'.toNat + (c.toNat - 55 - 10) = c.toNat by
        show 65 + (c.toNat - 55 - 10) = c.toNat; omega]
      exact Char.ofNat_toNat c
    case isFalse => simp at h

end CharLemmas

/-- The base32hex alphabet of RFC 4648 §7 (Table 4). -/
def alphabet : Alphabet 32 where
  toChar := toChar
  ofChar? := ofChar?
  ofChar?_toChar := ofChar?_toChar
  toChar_ne_pad := toChar_ne_pad
  ofChar?_eq_some := ofChar?_eq_some

/-- Encode a byte array as a base32hex string (RFC 4648 §7, with padding). -/
def encode (data : ByteArray) : String :=
  String.ofList (encodeList alphabet data.toList)

/-- Strictly decode a base32hex string. Returns `none` if the input is not
a canonical RFC 4648 §7 encoding. -/
def decode? (s : String) : Option ByteArray :=
  (decodeList alphabet s.toList).map fun bytes => ByteArray.mk bytes.toArray

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
  rw [encodeList_decodeList alphabet hl, String.ofList_toList]

/-- Encoding length, lifted to `ByteArray`/`String`. -/
theorem length_encode (data : ByteArray) :
    (encode data).length = 8 * ((data.size + 4) / 5) := by
  rw [encode, String.length_ofList, length_encodeList, ByteArray.length_toList]

/-- Decoding length, lifted to `ByteArray`/`String`. -/
theorem length_of_decode? {s : String} {data : ByteArray}
    (h : decode? s = some data) : s.length = 8 * ((data.size + 4) / 5) := by
  rw [← encode_decode? h, length_encode]

end Hex

end Rfc4648.Base32
