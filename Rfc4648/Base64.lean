import Std.Tactic.BVDecide
import Rfc4648.Util
import Rfc4648.Alphabet

/-!
# RFC 4648 §4 / §5 — Base 64 Encodings

Encoder and strict decoder for base64, parameterized over an
`Alphabet 64`. Two alphabets are provided: `Base64.alphabet` (§4,
`+`/`/`) and `Base64.Url.alphabet` (§5, `-`/`_`, URL and filename safe).
The codec and all its theorems are proved once, generically.

The specification `encodeList` / `decodeList` operates on `List UInt8` /
`List Char` by structural recursion over 3-byte / 4-character groups; all
theorems are proved against it. The user-facing `encode` and `decode?`
are allocation-free implementations over `ByteArray` and `String` — the
encoder writes table-driven UTF-8 bytes into a preallocated buffer, the
decoder pushes onto a `ByteArray` accumulator — each proved equal to the
specification (`encode_eq_model`, `decode?_eq_model`), so every theorem
transfers to them.

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

/-! ## The specification, parameterized over the alphabet -/

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

/-! ## Bounds on the 6-bit values produced by the encoder

These feed the alphabet lemmas and the byte-level table lookups. -/

private theorem v0_lt (b0 : UInt8) : b0 >>> 2 < 64 := by bv_decide

private theorem v1_lt (b0 b1 : UInt8) :
    ((b0 &&& 0x03) <<< 4) ||| (b1 >>> 4) < 64 := by bv_decide

private theorem v1p_lt (b0 : UInt8) : (b0 &&& 0x03) <<< 4 < 64 := by bv_decide

private theorem v2_lt (b1 b2 : UInt8) :
    ((b1 &&& 0x0F) <<< 2) ||| (b2 >>> 6) < 64 := by bv_decide

private theorem v2p_lt (b1 : UInt8) : (b1 &&& 0x0F) <<< 2 < 64 := by bv_decide

private theorem v3_lt (b2 : UInt8) : b2 &&& 0x3F < 64 := by bv_decide

/-! ## The implementation

`encodeList`/`decodeList` allocate a cons cell per character, so they
serve only as the specification. The definitions below are the real
codec: the encoder reads 3-byte groups straight from the input, looks
the alphabet's UTF-8 bytes up in a precomputed table, and pushes them
onto a buffer preallocated at the exact output size; the result is
wrapped as a `String` by the *unchecked* runtime constructor, whose
`IsValidUTF8` obligation is discharged by the proof that the bytes equal
the UTF-8 encoding of the specification's output. The decoder pushes
decoded bytes onto a `ByteArray` accumulator. -/

/-- The alphabet's characters as their single UTF-8 bytes. -/
private def mkTable (α : Alphabet 64) : ByteArray :=
  (List.ofFn fun i : Fin 64 => (α.toChar (UInt8.ofNat i.val)).val.toUInt8).toByteArray

/-- Tail-recursive base64 encoder: reads 3-byte groups directly from
`data` starting at `i`, pushing the alphabet's UTF-8 bytes from `tbl`
onto `acc`. -/
private def encodeGo (tbl : ByteArray) (data : ByteArray) (i : Nat) (acc : ByteArray) :
    ByteArray :=
  if h3 : i + 3 ≤ data.size then
    encodeGo tbl data (i + 3) <| (((acc.push
      (tbl.get! (data[i]'(by omega) >>> 2).toNat)).push
      (tbl.get! (((data[i]'(by omega) &&& 0x03) <<< 4) ||| (data[i + 1]'(by omega) >>> 4)).toNat)).push
      (tbl.get! (((data[i + 1]'(by omega) &&& 0x0F) <<< 2) ||| (data[i + 2]'(by omega) >>> 6)).toNat)).push
      (tbl.get! (data[i + 2]'(by omega) &&& 0x3F).toNat)
  else if h1 : data.size = i + 1 then
    (((acc.push
      (tbl.get! (data[i]'(by omega) >>> 2).toNat)).push
      (tbl.get! ((data[i]'(by omega) &&& 0x03) <<< 4).toNat)).push
      '='.val.toUInt8).push '='.val.toUInt8
  else if h2 : data.size = i + 2 then
    (((acc.push
      (tbl.get! (data[i]'(by omega) >>> 2).toNat)).push
      (tbl.get! (((data[i]'(by omega) &&& 0x03) <<< 4) ||| (data[i + 1]'(by omega) >>> 4)).toNat)).push
      (tbl.get! ((data[i + 1]'(by omega) &&& 0x0F) <<< 2).toNat)).push '='.val.toUInt8
  else acc
termination_by data.size - i

/-- Tail-recursive base64 decoder: consumes 4-character groups, pushing
decoded bytes onto `acc`. -/
private def decodeGo (α : Alphabet 64) : List Char → ByteArray → Option ByteArray
  | [], acc => some acc
  | c0 :: c1 :: c2 :: c3 :: rest, acc => do
    let v0 ← α.ofChar? c0
    let v1 ← α.ofChar? c1
    if c2 = '=' then
      if c3 = '=' ∧ rest = [] ∧ v1 &&& 0x0F = 0 then
        some (acc.push ((v0 <<< 2) ||| (v1 >>> 4)))
      else none
    else do
      let v2 ← α.ofChar? c2
      if c3 = '=' then
        if rest = [] ∧ v2 &&& 0x03 = 0 then
          some ((acc.push ((v0 <<< 2) ||| (v1 >>> 4))).push
            ((v1 <<< 4) ||| (v2 >>> 2)))
        else none
      else do
        let v3 ← α.ofChar? c3
        decodeGo α rest <| ((acc.push
          ((v0 <<< 2) ||| (v1 >>> 4))).push
          ((v1 <<< 4) ||| (v2 >>> 2))).push
          ((v2 <<< 6) ||| v3)
  | _, _ => none

/-! ### Equivalence with the specification -/

section Model

private theorem drop_two (data : ByteArray) (i : Nat) (h : i + 2 ≤ data.size) :
    data.toList.drop i =
      data[i]'(by omega) :: data[i + 1]'(by omega) :: data.toList.drop (i + 2) := by
  rw [drop_cons data i (by omega), drop_cons data (i + 1) (by omega)]

private theorem drop_three (data : ByteArray) (i : Nat) (h : i + 3 ≤ data.size) :
    data.toList.drop i =
      data[i]'(by omega) :: data[i + 1]'(by omega) :: data[i + 2]'(by omega) ::
        data.toList.drop (i + 3) := by
  rw [drop_cons data i (by omega), drop_cons data (i + 1) (by omega),
    drop_cons data (i + 1 + 1) (by omega)]

private theorem append_ofList_cons (s : String) (c : Char) (cs : List Char) :
    s ++ String.ofList (c :: cs) = (s.push c) ++ String.ofList cs :=
  str_ext (by simp [String.toList_append, String.toList_push])

private theorem append_ofList_nil (s : String) : s ++ String.ofList [] = s :=
  str_ext (by simp)

private theorem mkTable_get! (α : Alphabet 64) {v : UInt8} (hv : v < 64) :
    (mkTable α).get! v.toNat = (α.toChar v).val.toUInt8 := by
  have hvn : v.toNat < 64 := hv
  have hdata : (mkTable α).data.toList =
      List.ofFn fun i : Fin 64 => (α.toChar (UInt8.ofNat i.val)).val.toUInt8 :=
    List.toList_data_toByteArray
  have hsz : (mkTable α).data.size = 64 := by
    rw [← Array.length_toList, hdata, List.length_ofFn]
  rw [get!_eq, getElem!_pos _ _ (by omega), ← Array.getElem_toList,
    List.getElem_of_eq hdata, List.getElem_ofFn, UInt8.ofNat_toNat]

/-- The encoder computes the UTF-8 bytes of the specification's output:
if the accumulator holds the bytes of the string `sacc`, running the loop
from `i` yields the bytes of `sacc` followed by the encoding of the
remaining input. In particular the output is valid UTF-8. -/
private theorem encodeGo_eq (α : Alphabet 64)
    (h : ∀ v : UInt8, v < 64 → (α.toChar v).utf8Size = 1) (data : ByteArray)
    (i : Nat) (acc : ByteArray) (sacc : String) (hacc : acc = sacc.toByteArray) :
    encodeGo (mkTable α) data i acc =
      (sacc ++ String.ofList (encodeList α (data.toList.drop i))).toByteArray := by
  revert sacc hacc
  fun_induction encodeGo (mkTable α) data i acc with
  | case1 i acc h3 ih =>
    intro sacc hacc
    rw [drop_three data i (by omega)]
    simp only [encodeList, append_ofList_cons]
    refine ih _ ?_
    subst hacc
    rw [toByteArray_push_ascii _ _ (h _ (v3_lt _)),
      toByteArray_push_ascii _ _ (h _ (v2_lt _ _)),
      toByteArray_push_ascii _ _ (h _ (v1_lt _ _)),
      toByteArray_push_ascii _ _ (h _ (v0_lt _)),
      mkTable_get! α (v0_lt _), mkTable_get! α (v1_lt _ _),
      mkTable_get! α (v2_lt _ _), mkTable_get! α (v3_lt _)]
  | case2 i acc h3 h1 =>
    intro sacc hacc
    rw [drop_cons data i (by omega), drop_of_size_le data (i + 1) (by omega)]
    simp only [encodeList, append_ofList_cons, append_ofList_nil]
    subst hacc
    rw [toByteArray_push_ascii _ _ (by decide : ('=' : Char).utf8Size = 1),
      toByteArray_push_ascii _ _ (by decide : ('=' : Char).utf8Size = 1),
      toByteArray_push_ascii _ _ (h _ (v1p_lt _)),
      toByteArray_push_ascii _ _ (h _ (v0_lt _)),
      mkTable_get! α (v0_lt _), mkTable_get! α (v1p_lt _)]
  | case3 i acc h3 h1 h2 =>
    intro sacc hacc
    rw [drop_two data i (by omega), drop_of_size_le data (i + 2) (by omega)]
    simp only [encodeList, append_ofList_cons, append_ofList_nil]
    subst hacc
    rw [toByteArray_push_ascii _ _ (by decide : ('=' : Char).utf8Size = 1),
      toByteArray_push_ascii _ _ (h _ (v2p_lt _)),
      toByteArray_push_ascii _ _ (h _ (v1_lt _ _)),
      toByteArray_push_ascii _ _ (h _ (v0_lt _)),
      mkTable_get! α (v0_lt _), mkTable_get! α (v1_lt _ _),
      mkTable_get! α (v2p_lt _)]
  | case4 i acc h3 h1 h2 =>
    intro sacc hacc
    rw [drop_of_size_le data i (by omega)]
    simp only [encodeList, append_ofList_nil]
    exact hacc

/-- The encoder loop started on an empty buffer computes exactly the
UTF-8 bytes of the specification's output. -/
private theorem encodeGo_empty (α : Alphabet 64)
    (h : ∀ v : UInt8, v < 64 → (α.toChar v).utf8Size = 1) (data : ByteArray) :
    encodeGo (mkTable α) data 0 ByteArray.empty =
      (String.ofList (encodeList α data.toList)).toByteArray := by
  rw [encodeGo_eq α h data 0 ByteArray.empty "" rfl]
  exact congrArg String.toByteArray (str_ext (by simp))

private theorem decodeGo_eq (α : Alphabet 64) : ∀ (cs : List Char) (acc : ByteArray),
    decodeGo α cs acc = (decodeList α cs).map fun l => ⟨acc.data ++ l.toArray⟩
  | [], acc => by
    simp only [decodeGo, decodeList, Option.map_some]
    exact congrArg some (bext (by simp))
  | c0 :: c1 :: c2 :: c3 :: rest, acc => by
    simp only [decodeGo, decodeList, Option.bind_eq_bind]
    cases α.ofChar? c0 with
    | none => simp
    | some v0 =>
      cases α.ofChar? c1 with
      | none => simp
      | some v1 =>
        simp only [Option.bind_some]
        split
        · split
          · exact congrArg some (bext (by
              cases acc
              simp only [ByteArray.push]
              refine Array.toList_inj.mp ?_
              simp [-Array.toList_inj]))
          · simp
        · cases α.ofChar? c2 with
          | none => simp
          | some v2 =>
            simp only [Option.bind_some]
            split
            · split
              · exact congrArg some (bext (by
                  cases acc
                  simp only [ByteArray.push]
                  refine Array.toList_inj.mp ?_
                  simp [-Array.toList_inj]))
              · simp
            · cases α.ofChar? c3 with
              | none => simp
              | some v3 =>
                simp only [Option.bind_some,
                  decodeGo_eq α rest (((acc.push _).push _).push _)]
                cases decodeList α rest with
                | none => simp
                | some tail =>
                  simp only [Option.map_some]
                  exact congrArg some (bext (by
                    cases acc
                    simp only [ByteArray.push]
                    refine Array.toList_inj.mp ?_
                    simp [-Array.toList_inj]))
  | [_], _ => by simp [decodeGo, decodeList]
  | [_, _], _ => by simp [decodeGo, decodeList]
  | [_, _, _], _ => by simp [decodeGo, decodeList]

/-- The decoder loop started on an empty accumulator computes exactly the
specification's decoding. -/
private theorem decodeGo_empty (α : Alphabet 64) (s : String) :
    decodeGo α s.toList ByteArray.empty =
      (decodeList α s.toList).map fun l => ByteArray.mk l.toArray := by
  rw [decodeGo_eq]
  cases decodeList α s.toList with
  | none => rfl
  | some l =>
    simp only [Option.map_some]
    exact congrArg some (bext (by
      rw [show ByteArray.empty.data = #[] from rfl]
      simp))

end Model

/-! ## The user-facing codec -/

section Ascii

set_option maxRecDepth 4096

private theorem alphabet_ascii : ∀ v : UInt8, v < 64 →
    (alphabet.toChar v).utf8Size = 1 :=
  uint8_all (by decide)

end Ascii

/-- The §4 alphabet table, computed once at initialization. -/
private def stdTable : ByteArray := mkTable alphabet

/-- Encode a byte array as a base64 string (RFC 4648 §4, with padding). -/
def encode (data : ByteArray) : String :=
  String.ofByteArray
    (encodeGo stdTable data 0 (ByteArray.emptyWithCapacity (4 * ((data.size + 2) / 3))))
    (by
      show (encodeGo (mkTable alphabet) data 0 _).IsValidUTF8
      rw [emptyWithCapacity_eq, encodeGo_empty alphabet alphabet_ascii]
      exact (String.ofList (encodeList alphabet data.toList)).isValidUTF8)

/-- Strictly decode a base64 string. Returns `none` if the input is not a
canonical RFC 4648 §4 encoding. -/
def decode? (s : String) : Option ByteArray :=
  decodeGo alphabet s.toList ByteArray.empty

/-- `encode` computes exactly the specification `encodeList`; encoder
theorems transfer through this equality. -/
theorem encode_eq_model (data : ByteArray) :
    encode data = String.ofList (encodeList alphabet data.toList) := by
  rw [← String.toByteArray_inj]
  show encodeGo (mkTable alphabet) data 0 (ByteArray.emptyWithCapacity _) = _
  rw [emptyWithCapacity_eq]
  exact encodeGo_empty alphabet alphabet_ascii data

/-- `decode?` computes exactly the specification `decodeList`; decoder
theorems transfer through this equality. -/
theorem decode?_eq_model (s : String) :
    decode? s = (decodeList alphabet s.toList).map fun bytes => ByteArray.mk bytes.toArray :=
  decodeGo_empty alphabet s

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
  simp only [decode?_eq_model, encode_eq_model, String.toList_ofList,
    decodeList_encodeList, Option.map_some, ByteArray.mk_toList_toArray]

/-- Canonicity, lifted to `ByteArray`/`String`. -/
theorem encode_decode? {s : String} {data : ByteArray}
    (h : decode? s = some data) : encode data = s := by
  rw [decode?_eq_model] at h
  simp only [Option.map_eq_some_iff] at h
  obtain ⟨l, hl, hdata⟩ := h
  subst hdata
  simp only [encode_eq_model, ByteArray.toList_mk]
  rw [encodeList_decodeList alphabet hl, String.ofList_toList]

end RoundTrip

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

section Ascii

set_option maxRecDepth 4096

private theorem alphabet_ascii : ∀ v : UInt8, v < 64 →
    (alphabet.toChar v).utf8Size = 1 :=
  uint8_all (by decide)

end Ascii

/-- The §5 alphabet table, computed once at initialization. -/
private def urlTable : ByteArray := mkTable alphabet

/-- Encode a byte array as a base64url string (RFC 4648 §5, with padding). -/
def encode (data : ByteArray) : String :=
  String.ofByteArray
    (encodeGo urlTable data 0 (ByteArray.emptyWithCapacity (4 * ((data.size + 2) / 3))))
    (by
      show (encodeGo (mkTable alphabet) data 0 _).IsValidUTF8
      rw [emptyWithCapacity_eq, encodeGo_empty alphabet alphabet_ascii]
      exact (String.ofList (encodeList alphabet data.toList)).isValidUTF8)

/-- Strictly decode a base64url string. Returns `none` if the input is not
a canonical RFC 4648 §5 encoding (including if padding is omitted). -/
def decode? (s : String) : Option ByteArray :=
  decodeGo alphabet s.toList ByteArray.empty

/-- `encode` computes exactly the specification `encodeList`; encoder
theorems transfer through this equality. -/
theorem encode_eq_model (data : ByteArray) :
    encode data = String.ofList (encodeList alphabet data.toList) := by
  rw [← String.toByteArray_inj]
  show encodeGo (mkTable alphabet) data 0 (ByteArray.emptyWithCapacity _) = _
  rw [emptyWithCapacity_eq]
  exact encodeGo_empty alphabet alphabet_ascii data

/-- `decode?` computes exactly the specification `decodeList`; decoder
theorems transfer through this equality. -/
theorem decode?_eq_model (s : String) :
    decode? s = (decodeList alphabet s.toList).map fun bytes => ByteArray.mk bytes.toArray :=
  decodeGo_empty alphabet s

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
  simp only [decode?_eq_model, encode_eq_model, String.toList_ofList,
    decodeList_encodeList, Option.map_some, ByteArray.mk_toList_toArray]

/-- Canonicity, lifted to `ByteArray`/`String`. -/
theorem encode_decode? {s : String} {data : ByteArray}
    (h : decode? s = some data) : encode data = s := by
  rw [decode?_eq_model] at h
  simp only [Option.map_eq_some_iff] at h
  obtain ⟨l, hl, hdata⟩ := h
  subst hdata
  simp only [encode_eq_model, ByteArray.toList_mk]
  rw [encodeList_decodeList alphabet hl, String.ofList_toList]

end Url

end Rfc4648.Base64
