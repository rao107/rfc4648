import Std.Tactic.BVDecide
import Rfc4648.Util
import Rfc4648.Alphabet

/-!
# RFC 4648 §4 / §5 — Base 64 Encodings

Encoder and strict decoder for base64, parameterized over an
`Alphabet 64`. Two alphabets are provided: `Base64.alphabet` (§4,
`+`/`/`) and `Base64.Url.alphabet` (§5, `-`/`_`, URL and filename safe).
The codec and all its theorems are proved once, generically.

The core functions `encodeList` and `decodeList` operate on `List UInt8` /
`List Char` by structural recursion over 3-byte / 4-character groups.
`encode` and `decode?` are the user-facing wrappers over `ByteArray` and
`String`.

The decoder is strict in the sense of RFC 4648 §3.5 and §12: it rejects
characters outside the alphabet, misplaced or missing padding, and
non-zero pad bits. Consequently `decode?` accepts exactly the outputs of
`encode`. Padding is always required, even for the §5 alphabet (which
some protocols use unpadded).
-/

namespace Rfc4648.Base64

/-! ## The §4 alphabet -/

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

section CharLemmas

set_option maxRecDepth 4096

theorem ofChar?_toChar : ∀ v : UInt8, v < 64 → ofChar? (toChar v) = some v :=
  uint8_all (by decide)

theorem toChar_ne_pad : ∀ v : UInt8, v < 64 → toChar v ≠ '=' :=
  uint8_all (by decide)

theorem ofChar?_eq_some {c : Char} {v : UInt8} (h : ofChar? c = some v) :
    v < 64 ∧ toChar v = c := by
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
    refine ⟨by rw [UInt8.lt_iff_toNat_lt, hval]; show c.toNat - 65 < 64; omega, ?_⟩
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
      refine ⟨by rw [UInt8.lt_iff_toNat_lt, hval]; show c.toNat - 71 < 64; omega, ?_⟩
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
        refine ⟨by rw [UInt8.lt_iff_toNat_lt, hval]; show c.toNat + 4 < 64; omega, ?_⟩
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

end CharLemmas

/-- The base64 alphabet of RFC 4648 §4 (Table 1). -/
def alphabet : Alphabet 64 where
  toChar := toChar
  ofChar? := ofChar?
  ofChar?_toChar := ofChar?_toChar
  toChar_ne_pad := toChar_ne_pad
  ofChar?_eq_some := ofChar?_eq_some

/-! ## The codec, parameterized over the alphabet -/

/-- Encode bytes as base64 characters, processing one 24-bit group
(3 bytes → 4 characters) per step. A final group of 1 or 2 bytes is
zero-padded to a whole number of 6-bit values and the output filled to
4 characters with `=` (RFC 4648 §4). -/
def encodeList (α : Alphabet 64) : List UInt8 → List Char
  | [] => []
  | [b0] =>
    [α.toChar (b0 >>> 2),
     α.toChar ((b0 &&& 0x03) <<< 4),
     '=', '=']
  | [b0, b1] =>
    [α.toChar (b0 >>> 2),
     α.toChar (((b0 &&& 0x03) <<< 4) ||| (b1 >>> 4)),
     α.toChar ((b1 &&& 0x0F) <<< 2),
     '=']
  | b0 :: b1 :: b2 :: rest =>
    α.toChar (b0 >>> 2) ::
    α.toChar (((b0 &&& 0x03) <<< 4) ||| (b1 >>> 4)) ::
    α.toChar (((b1 &&& 0x0F) <<< 2) ||| (b2 >>> 6)) ::
    α.toChar (b2 &&& 0x3F) ::
    encodeList α rest

/-- Strictly decode base64 characters, one 4-character group per step.
Returns `none` unless the input is a canonical encoding: length a multiple
of 4, padding only in the final group, and all pad bits zero. -/
def decodeList (α : Alphabet 64) : List Char → Option (List UInt8)
  | [] => some []
  | c0 :: c1 :: c2 :: c3 :: rest => do
    let v0 ← α.ofChar? c0
    let v1 ← α.ofChar? c1
    if c2 = '=' then
      -- "xx==": one output byte; the low 4 bits of v1 are pad bits.
      if c3 = '=' ∧ rest = [] ∧ v1 &&& 0x0F = 0 then
        some [(v0 <<< 2) ||| (v1 >>> 4)]
      else none
    else do
      let v2 ← α.ofChar? c2
      if c3 = '=' then
        -- "xxx=": two output bytes; the low 2 bits of v2 are pad bits.
        if rest = [] ∧ v2 &&& 0x03 = 0 then
          some [(v0 <<< 2) ||| (v1 >>> 4),
                (v1 <<< 4) ||| (v2 >>> 2)]
        else none
      else do
        let v3 ← α.ofChar? c3
        let tail ← decodeList α rest
        some (((v0 <<< 2) ||| (v1 >>> 4)) ::
              ((v1 <<< 4) ||| (v2 >>> 2)) ::
              ((v2 <<< 6) ||| v3) ::
              tail)
  | _ => none

/-- Encode a byte array as a base64 string (RFC 4648 §4, with padding). -/
def encode (data : ByteArray) : String :=
  String.ofList (encodeList alphabet data.toList)

/-- Strictly decode a base64 string. Returns `none` if the input is not a
canonical RFC 4648 §4 encoding. -/
def decode? (s : String) : Option ByteArray :=
  (decodeList alphabet s.toList).map fun bytes => ByteArray.mk bytes.toArray

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

`decodeList_encodeList` / `decode?_encode`: decoding an encoding gives back
the input. `encodeList_decodeList` / `encode_decode?`: anything the strict
decoder accepts is the encoding of its output. The list-level theorems
hold for any `Alphabet 64`. -/

section RoundTrip

/-! Bounds on the 6-bit values produced by the encoder, for feeding the
alphabet lemmas. -/

private theorem v0_lt (b0 : UInt8) : b0 >>> 2 < 64 := by bv_decide

private theorem v1_lt (b0 b1 : UInt8) :
    ((b0 &&& 0x03) <<< 4) ||| (b1 >>> 4) < 64 := by bv_decide

private theorem v1p_lt (b0 : UInt8) : (b0 &&& 0x03) <<< 4 < 64 := by bv_decide

private theorem v2_lt (b1 b2 : UInt8) :
    ((b1 &&& 0x0F) <<< 2) ||| (b2 >>> 6) < 64 := by bv_decide

private theorem v2p_lt (b1 : UInt8) : (b1 &&& 0x0F) <<< 2 < 64 := by bv_decide

private theorem v3_lt (b2 : UInt8) : b2 &&& 0x3F < 64 := by bv_decide

/-- Round-trip: strictly decoding an encoding yields the original bytes. -/
theorem decodeList_encodeList (α : Alphabet 64) : ∀ bs : List UInt8,
    decodeList α (encodeList α bs) = some bs
  | [] => rfl
  | [b0] => by
    simp only [encodeList, decodeList,
      α.ofChar?_toChar _ (v0_lt b0), α.ofChar?_toChar _ (v1p_lt b0),
      Option.bind_eq_bind, Option.bind_some]
    rw [if_pos trivial, if_pos ⟨trivial, trivial, by bv_decide⟩]
    have e0 : ((b0 >>> 2) <<< 2) ||| (((b0 &&& 0x03) <<< 4) >>> 4) = b0 := by
      bv_decide
    rw [e0]
  | [b0, b1] => by
    simp only [encodeList, decodeList,
      α.ofChar?_toChar _ (v0_lt b0), α.ofChar?_toChar _ (v1_lt b0 b1),
      α.ofChar?_toChar _ (v2p_lt b1),
      Option.bind_eq_bind, Option.bind_some]
    rw [if_neg (α.toChar_ne_pad _ (v2p_lt b1)), if_pos trivial,
      if_pos ⟨trivial, by bv_decide⟩]
    have e0 : ((b0 >>> 2) <<< 2) |||
        ((((b0 &&& 0x03) <<< 4) ||| (b1 >>> 4)) >>> 4) = b0 := by bv_decide
    have e1 : ((((b0 &&& 0x03) <<< 4) ||| (b1 >>> 4)) <<< 4) |||
        (((b1 &&& 0x0F) <<< 2) >>> 2) = b1 := by bv_decide
    rw [e0, e1]
  | b0 :: b1 :: b2 :: rest => by
    simp only [encodeList, decodeList,
      α.ofChar?_toChar _ (v0_lt b0), α.ofChar?_toChar _ (v1_lt b0 b1),
      α.ofChar?_toChar _ (v2_lt b1 b2), α.ofChar?_toChar _ (v3_lt b2),
      Option.bind_eq_bind, Option.bind_some,
      decodeList_encodeList α rest]
    rw [if_neg (α.toChar_ne_pad _ (v2_lt b1 b2)),
      if_neg (α.toChar_ne_pad _ (v3_lt b2))]
    have e0 : ((b0 >>> 2) <<< 2) |||
        ((((b0 &&& 0x03) <<< 4) ||| (b1 >>> 4)) >>> 4) = b0 := by bv_decide
    have e1 : ((((b0 &&& 0x03) <<< 4) ||| (b1 >>> 4)) <<< 4) |||
        ((((b1 &&& 0x0F) <<< 2) ||| (b2 >>> 6)) >>> 2) = b1 := by bv_decide
    have e2 : ((((b1 &&& 0x0F) <<< 2) ||| (b2 >>> 6)) <<< 6) |||
        (b2 &&& 0x3F) = b2 := by bv_decide
    rw [e0, e1, e2]

/-- Canonicity: every string the strict decoder accepts is the encoding of
the bytes it returns. -/
theorem encodeList_decodeList (α : Alphabet 64) : ∀ {cs : List Char} {bs : List UInt8},
    decodeList α cs = some bs → encodeList α bs = cs
  | [], _, h => by
    simp only [decodeList, Option.some.injEq] at h
    simp [← h, encodeList]
  | _c0 :: _c1 :: c2 :: c3 :: rest, bs, h => by
    simp only [decodeList, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨v0, hv0, v1, hv1, h⟩ := h
    obtain ⟨hlt0, hc0⟩ := α.ofChar?_eq_some hv0
    obtain ⟨hlt1, hc1⟩ := α.ofChar?_eq_some hv1
    split at h
    case isTrue hc2 =>
      split at h
      case isTrue hcond =>
        obtain ⟨hc3, hrest, hpad⟩ := hcond
        injection h with h
        subst h
        subst hc2 hc3 hrest
        have e0 : ((v0 <<< 2) ||| (v1 >>> 4)) >>> 2 = v0 := by bv_decide
        have e1 : (((v0 <<< 2) ||| (v1 >>> 4)) &&& 0x03) <<< 4 = v1 := by bv_decide
        simp only [encodeList]
        rw [e0, e1, hc0, hc1]
      case isFalse => simp at h
    case isFalse hc2 =>
      simp only [Option.bind_eq_some_iff] at h
      obtain ⟨v2, hv2, h⟩ := h
      obtain ⟨hlt2, hc2'⟩ := α.ofChar?_eq_some hv2
      split at h
      case isTrue hc3 =>
        split at h
        case isTrue hcond =>
          obtain ⟨hrest, hpad⟩ := hcond
          injection h with h
          subst h
          subst hc3 hrest
          have e0 : ((v0 <<< 2) ||| (v1 >>> 4)) >>> 2 = v0 := by bv_decide
          have e1 : ((((v0 <<< 2) ||| (v1 >>> 4)) &&& 0x03) <<< 4) |||
              (((v1 <<< 4) ||| (v2 >>> 2)) >>> 4) = v1 := by bv_decide
          have e2 : (((v1 <<< 4) ||| (v2 >>> 2)) &&& 0x0F) <<< 2 = v2 := by
            bv_decide
          simp only [encodeList]
          rw [e0, e1, e2, hc0, hc1, hc2']
        case isFalse => simp at h
      case isFalse hc3 =>
        simp only [Option.bind_eq_some_iff, Option.some.injEq] at h
        obtain ⟨v3, hv3, tail, htail, hbs⟩ := h
        obtain ⟨hlt3, hc3'⟩ := α.ofChar?_eq_some hv3
        subst hbs
        have e0 : ((v0 <<< 2) ||| (v1 >>> 4)) >>> 2 = v0 := by bv_decide
        have e1 : ((((v0 <<< 2) ||| (v1 >>> 4)) &&& 0x03) <<< 4) |||
            (((v1 <<< 4) ||| (v2 >>> 2)) >>> 4) = v1 := by bv_decide
        have e2 : ((((v1 <<< 4) ||| (v2 >>> 2)) &&& 0x0F) <<< 2) |||
            (((v2 <<< 6) ||| v3) >>> 6) = v2 := by bv_decide
        have e3 : ((v2 <<< 6) ||| v3) &&& 0x3F = v3 := by bv_decide
        simp only [encodeList]
        rw [e0, e1, e2, e3, encodeList_decodeList α htail, hc0, hc1, hc2', hc3']
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
  rw [encodeList_decodeList alphabet hl, String.ofList_toList]

end RoundTrip

/-! ## Output length -/

section Length

/-- The encoding of `n` bytes has exactly `4 * ((n + 2) / 3)` characters. -/
theorem length_encodeList (α : Alphabet 64) : ∀ bs : List UInt8,
    (encodeList α bs).length = 4 * ((bs.length + 2) / 3)
  | [] => rfl
  | [_] => by simp [encodeList]
  | [_, _] => by simp [encodeList]
  | b0 :: b1 :: b2 :: rest => by
    simp only [encodeList, List.length_cons, length_encodeList α rest]
    omega

/-- Anything the strict decoder accepts has the padded encoding length of
its output. -/
theorem length_of_decodeList {α : Alphabet 64} {cs : List Char} {bs : List UInt8}
    (h : decodeList α cs = some bs) : cs.length = 4 * ((bs.length + 2) / 3) := by
  rw [← encodeList_decodeList α h, length_encodeList]

/-- Anything the strict decoder accepts has length divisible by 4. -/
theorem length_of_decodeList_mod {α : Alphabet 64} {cs : List Char} {bs : List UInt8}
    (h : decodeList α cs = some bs) : cs.length % 4 = 0 := by
  rw [length_of_decodeList h]
  omega

/-- Encoding length, lifted to `ByteArray`/`String`. -/
theorem length_encode (data : ByteArray) :
    (encode data).length = 4 * ((data.size + 2) / 3) := by
  rw [encode, String.length_ofList, length_encodeList, ByteArray.length_toList]

/-- Decoding length, lifted to `ByteArray`/`String`. -/
theorem length_of_decode? {s : String} {data : ByteArray}
    (h : decode? s = some data) : s.length = 4 * ((data.size + 2) / 3) := by
  rw [← encode_decode? h, length_encode]

end Length

/-! ## RFC 4648 §5 — Base 64 with URL and filename safe alphabet

The same verified codec applied to the §5 alphabet: value 62 maps to `-`
and 63 to `_`. Padding is retained: although §5 permits omitting it in
some contexts, the canonical form keeps `=`, and the strict decoder here
requires it. -/

namespace Url

/-- Map a 6-bit value to its character in the base64url alphabet
(RFC 4648 Table 2): `A`–`Z`, `a`–`z`, `0`–`9`, `-`, `_`. -/
def toChar (v : UInt8) : Char :=
  if v < 26 then Char.ofNat ('A'.toNat + v.toNat)
  else if v < 52 then Char.ofNat ('a'.toNat + (v.toNat - 26))
  else if v < 62 then Char.ofNat ('0'.toNat + (v.toNat - 52))
  else if v = 62 then '-'
  else '_'

/-- Map a character to its 6-bit value, or `none` if it is not in the
base64url alphabet. Inverse of `toChar`. -/
def ofChar? (c : Char) : Option UInt8 :=
  if 'A' ≤ c ∧ c ≤ 'Z' then some (c.toNat.toUInt8 - 'A'.toNat.toUInt8)
  else if 'a' ≤ c ∧ c ≤ 'z' then some (c.toNat.toUInt8 - 'a'.toNat.toUInt8 + 26)
  else if '0' ≤ c ∧ c ≤ '9' then some (c.toNat.toUInt8 - '0'.toNat.toUInt8 + 52)
  else if c = '-' then some 62
  else if c = '_' then some 63
  else none

section CharLemmas

set_option maxRecDepth 4096

theorem ofChar?_toChar : ∀ v : UInt8, v < 64 → ofChar? (toChar v) = some v :=
  uint8_all (by decide)

theorem toChar_ne_pad : ∀ v : UInt8, v < 64 → toChar v ≠ '=' :=
  uint8_all (by decide)

theorem ofChar?_eq_some {c : Char} {v : UInt8} (h : ofChar? c = some v) :
    v < 64 ∧ toChar v = c := by
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
    refine ⟨by rw [UInt8.lt_iff_toNat_lt, hval]; show c.toNat - 65 < 64; omega, ?_⟩
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
      refine ⟨by rw [UInt8.lt_iff_toNat_lt, hval]; show c.toNat - 71 < 64; omega, ?_⟩
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
        refine ⟨by rw [UInt8.lt_iff_toNat_lt, hval]; show c.toNat + 4 < 64; omega, ?_⟩
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
        case isTrue hdash =>
          injection h with hv
          subst hv
          subst hdash
          exact ⟨by decide, by decide⟩
        case isFalse =>
          split at h
          case isTrue hunder =>
            injection h with hv
            subst hv
            subst hunder
            exact ⟨by decide, by decide⟩
          case isFalse => simp at h

end CharLemmas

/-- The base64url alphabet of RFC 4648 §5 (Table 2). -/
def alphabet : Alphabet 64 where
  toChar := toChar
  ofChar? := ofChar?
  ofChar?_toChar := ofChar?_toChar
  toChar_ne_pad := toChar_ne_pad
  ofChar?_eq_some := ofChar?_eq_some

/-- Encode a byte array as a base64url string (RFC 4648 §5, with padding). -/
def encode (data : ByteArray) : String :=
  String.ofList (encodeList alphabet data.toList)

/-- Strictly decode a base64url string. Returns `none` if the input is not
a canonical RFC 4648 §5 encoding (including if padding is omitted). -/
def decode? (s : String) : Option ByteArray :=
  (decodeList alphabet s.toList).map fun bytes => ByteArray.mk bytes.toArray

#guard encode "".toUTF8 = ""
#guard encode "fooba".toUTF8 = "Zm9vYmE="
#guard encode "foobar".toUTF8 = "Zm9vYmFy"
#guard encode (ByteArray.mk #[0xFB, 0xEF]) = "--8="
#guard encode (ByteArray.mk #[0xFF, 0xFF, 0xFF]) = "____"

#guard (decode? "--8=").map ByteArray.toList = some [0xFB, 0xEF]
#guard (decode? "____").map ByteArray.toList = some [0xFF, 0xFF, 0xFF]
#guard (decode? "Zm9vYmFy").map ByteArray.toList = some "foobar".toUTF8.toList

#guard (decode? "++8=").isNone   -- §4 alphabet is rejected
#guard (decode? "//8=").isNone
#guard (decode? "Zg").isNone     -- omitted padding is rejected

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
    (encode data).length = 4 * ((data.size + 2) / 3) := by
  rw [encode, String.length_ofList, length_encodeList, ByteArray.length_toList]

/-- Decoding length, lifted to `ByteArray`/`String`. -/
theorem length_of_decode? {s : String} {data : ByteArray}
    (h : decode? s = some data) : s.length = 4 * ((data.size + 2) / 3) := by
  rw [← encode_decode? h, length_encode]

end Url

end Rfc4648.Base64
