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
are byte-level implementations over `ByteArray` and `String` — the
encoder writes table-driven UTF-8 bytes into a preallocated buffer, the
decoder reads the string's UTF-8 bytes through a 256-entry inverse
table — each proved equal to the specification (`encode_eq_model`,
`decode?_eq_model`), so every theorem transfers to them.

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

/-- The alphabet accepts only ASCII characters. -/
theorem ofChar?_ascii {c : Char} {v : UInt8} (h : ofChar? c = some v) :
    c.toNat < 128 := by
  unfold ofChar? at h
  split at h
  case isTrue h' => have : c.toNat ≤ 90 := h'.2; omega
  case isFalse =>
    split at h
    case isTrue h' => have : c.toNat ≤ 122 := h'.2; omega
    case isFalse =>
      split at h
      case isTrue h' => have : c.toNat ≤ 57 := h'.2; omega
      case isFalse =>
        split at h
        case isTrue h' => subst h'; decide
        case isFalse =>
          split at h
          case isTrue h' => subst h'; decide
          case isFalse => simp at h

theorem ofChar?_eq_some {c : Char} {v : UInt8} (h : ofChar? c = some v) :
    v < 64 ∧ toChar v = c := by
  -- The accepted characters are ASCII, so `c` is one of 128 characters
  -- and the claim reduces to an exhaustive check.
  have hall := char_all_lt
    (P := fun c => ((ofChar? c).all fun v => v < 64 && toChar v == c) = true)
    (by decide) c (ofChar?_ascii h)
  rw [h] at hall
  simpa using hall

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
the UTF-8 encoding of the specification's output. The decoder
(`decodeGoB` below) reads the string's UTF-8 bytes through the inverse
table; `decodeGo`, which walks the character list, is the intermediate
model both are compared against. -/

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

private theorem mkTable_get! (α : Alphabet 64) {v : UInt8} (hv : v < 64) :
    (mkTable α).get! v.toNat = (α.toChar v).val.toUInt8 := by
  have h : v.toNat < 64 := hv
  unfold mkTable
  rw [get!_ofFn_toByteArray _ h, UInt8.ofNat_toNat]

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
    exact congrArg some (ByteArray.ext (by simp))
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
          · exact congrArg some (ByteArray.ext (by simp [ByteArray.data_push]))
          · simp
        · cases α.ofChar? c2 with
          | none => simp
          | some v2 =>
            simp only [Option.bind_some]
            split
            · split
              · exact congrArg some (ByteArray.ext (by
                  simp [ByteArray.data_push, ← Array.toList_inj]))
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
                  exact congrArg some (ByteArray.ext (by simp [ByteArray.data_push]))
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
    exact congrArg some (ByteArray.ext (by simp [ByteArray.data_empty]))

end Model

/-! ### Byte-level decoder

The character-level `decodeGo` walks a `List Char` (allocated by
`String.toList`) and runs the `ofChar?` comparison chain per character.
The decoder below reads the string's UTF-8 bytes directly and looks
6-bit values up in the 256-entry inverse table `mkDTable`, with `0xFF`
marking non-alphabet bytes. It never decodes UTF-8: the table rejects
every byte `≥ 0x80`, and in valid UTF-8 a byte `< 0x80` *is* a whole
ASCII character, so accepted bytes are in one-to-one correspondence
with the characters of the specification (`decodeGoB_eq`). -/

/-- Tail-recursive byte-level base64 decoder: reads 4 input bytes per
step from `bs` starting at `i`, looks their 6-bit values up in the
inverse table `dtbl` (`0xFF` = reject), and pushes decoded bytes onto
`acc`. `61` is `'='`. -/
private def decodeGoB (dtbl : ByteArray) (bs : ByteArray) (i : Nat) (acc : ByteArray) :
    Option ByteArray :=
  if h4 : i + 4 ≤ bs.size then
    let v0 := dtbl.get! (bs[i]'(by omega)).toNat
    let v1 := dtbl.get! (bs[i + 1]'(by omega)).toNat
    if v0 = 0xFF ∨ v1 = 0xFF then none
    else if bs[i + 2]'(by omega) = 61 then
      if bs[i + 3]'(by omega) = 61 ∧ i + 4 = bs.size ∧ v1 &&& 0x0F = 0 then
        some (acc.push ((v0 <<< 2) ||| (v1 >>> 4)))
      else none
    else
      let v2 := dtbl.get! (bs[i + 2]'(by omega)).toNat
      if v2 = 0xFF then none
      else if bs[i + 3]'(by omega) = 61 then
        if i + 4 = bs.size ∧ v2 &&& 0x03 = 0 then
          some ((acc.push ((v0 <<< 2) ||| (v1 >>> 4))).push
            ((v1 <<< 4) ||| (v2 >>> 2)))
        else none
      else
        let v3 := dtbl.get! (bs[i + 3]'(by omega)).toNat
        if v3 = 0xFF then none
        else
          decodeGoB dtbl bs (i + 4) <| ((acc.push
            ((v0 <<< 2) ||| (v1 >>> 4))).push
            ((v1 <<< 4) ||| (v2 >>> 2))).push
            ((v2 <<< 6) ||| v3)
  else if i = bs.size then some acc else none
termination_by bs.size - i

section ByteDecoder

variable {α : Alphabet 64}
  (hascii : ∀ {c : Char} {v : UInt8}, α.ofChar? c = some v → c.toNat < 128)

include hascii

/-- The byte-level decoder computes the character-level decoder: if the
bytes from position `i` on are the UTF-8 encoding of the characters `l`,
the two agree. -/
private theorem decodeGoB_eq :
    ∀ (l : List Char) (bs : ByteArray) (i : Nat) (acc : ByteArray),
      i ≤ bs.size → bs.toList.drop i = (l.utf8Encode).toList →
      decodeGoB (mkDTable α) bs i acc = decodeGo α l acc
  | [] => by
    intro bs i acc hi hbs
    have hie : i = bs.size := (drop_utf8_nil_iff hi hbs).mpr rfl
    rw [decodeGoB.eq_def, dif_neg (by omega), if_pos hie]
    rfl
  | [c0] => by
    intro bs i acc hi hbs
    rw [show decodeGo α [c0] acc = none from by simp [decodeGo]]
    · by_cases h4 : i + 4 ≤ bs.size
      · rw [decodeGoB.eq_def, dif_pos h4]
        cases hv0 : α.ofChar? c0 with
        | some v0 =>
          obtain ⟨h0, -, -, hbs1⟩ := step_some hascii hv0 hbs
          have := (drop_utf8_nil_iff (j := i + 1) h0 hbs1).mpr rfl
          exact absurd h4 (by omega)
        | none =>
          obtain ⟨h0, hlk0⟩ := step_none hascii hv0 hbs
          simp [hlk0]
      · have hne : i ≠ bs.size := fun h =>
          absurd ((drop_utf8_nil_iff hi hbs).mp h) (by simp)
        rw [decodeGoB.eq_def, dif_neg h4, if_neg hne]
  | [c0, c1] => by
    intro bs i acc hi hbs
    rw [show decodeGo α [c0, c1] acc = none from by simp [decodeGo]]
    · by_cases h4 : i + 4 ≤ bs.size
      · rw [decodeGoB.eq_def, dif_pos h4]
        cases hv0 : α.ofChar? c0 with
        | none =>
          obtain ⟨h0, hlk0⟩ := step_none hascii hv0 hbs
          simp [hlk0]
        | some v0 =>
          obtain ⟨h0, hlk0, hb0ne, hbs1⟩ := step_some hascii hv0 hbs
          cases hv1 : α.ofChar? c1 with
          | none =>
            obtain ⟨h1, hlk1⟩ := step_none hascii hv1 hbs1
            simp [hlk1]
          | some v1 =>
            obtain ⟨h1, -, -, hbs2⟩ := step_some hascii hv1 hbs1
            have := (drop_utf8_nil_iff (j := i + 2) h1 hbs2).mpr rfl
            exact absurd h4 (by omega)
      · have hne : i ≠ bs.size := fun h =>
          absurd ((drop_utf8_nil_iff hi hbs).mp h) (by simp)
        rw [decodeGoB.eq_def, dif_neg h4, if_neg hne]
  | [c0, c1, c2] => by
    intro bs i acc hi hbs
    rw [show decodeGo α [c0, c1, c2] acc = none from by simp [decodeGo]]
    · by_cases h4 : i + 4 ≤ bs.size
      · rw [decodeGoB.eq_def, dif_pos h4]
        cases hv0 : α.ofChar? c0 with
        | none =>
          obtain ⟨h0, hlk0⟩ := step_none hascii hv0 hbs
          simp [hlk0]
        | some v0 =>
          obtain ⟨h0, hlk0, hb0ne, hbs1⟩ := step_some hascii hv0 hbs
          cases hv1 : α.ofChar? c1 with
          | none =>
            obtain ⟨h1, hlk1⟩ := step_none hascii hv1 hbs1
            simp [hlk1]
          | some v1 =>
            obtain ⟨h1, hlk1, hb1ne, hbs2⟩ := step_some hascii hv1 hbs1
            by_cases hc2 : c2 = '='
            · subst hc2
              obtain ⟨h2, -, hbs3⟩ := step_pad hbs2
              have := (drop_utf8_nil_iff (j := i + 3) h2 hbs3).mpr rfl
              exact absurd h4 (by omega)
            · simp only [hlk0, hlk1]
              rw [if_neg (by
                simp [ne_ff_of_some (α := α) hv0, ne_ff_of_some (α := α) hv1])]
              cases hv2 : α.ofChar? c2 with
              | none =>
                obtain ⟨h2, hlk2, hb2ne⟩ := step_bad hascii hv2 hc2 hbs2
                rw [if_neg (fun h61 => hb2ne h61)]
                simp [hlk2]
              | some v2 =>
                obtain ⟨h2, -, -, hbs3⟩ := step_some hascii hv2 hbs2
                have := (drop_utf8_nil_iff (j := i + 3) h2 hbs3).mpr rfl
                exact absurd h4 (by omega)
      · have hne : i ≠ bs.size := fun h =>
          absurd ((drop_utf8_nil_iff hi hbs).mp h) (by simp)
        rw [decodeGoB.eq_def, dif_neg h4, if_neg hne]
  | c0 :: c1 :: c2 :: c3 :: rest => by
    intro bs i acc hi hbs
    -- four characters are at least four bytes, so the four-byte branch runs
    have hlen : i + 4 ≤ bs.size := by
      have hl := congrArg List.length hbs
      rw [List.length_drop, ByteArray.length_toList, ByteArray.length_toList] at hl
      have hge := length_le_size_utf8Encode (c0 :: c1 :: c2 :: c3 :: rest)
      simp only [List.length_cons] at hge
      omega
    rw [decodeGoB.eq_def, dif_pos hlen]
    cases hv0 : α.ofChar? c0 with
    | none =>
      obtain ⟨h0, hlk0⟩ := step_none hascii hv0 hbs
      simp [hlk0, decodeGo, hv0]
    | some v0 =>
      obtain ⟨h0, hlk0, hb0ne, hbs1⟩ := step_some hascii hv0 hbs
      cases hv1 : α.ofChar? c1 with
      | none =>
        obtain ⟨h1, hlk1⟩ := step_none hascii hv1 hbs1
        simp [hlk1, decodeGo, hv0, hv1]
      | some v1 =>
        obtain ⟨h1, hlk1, hb1ne, hbs2⟩ := step_some hascii hv1 hbs1
        simp only [decodeGo, hv0, hv1, Option.bind_eq_bind, Option.bind_some,
          hlk0, hlk1]
        rw [if_neg (by
          simp [ne_ff_of_some (α := α) hv0, ne_ff_of_some (α := α) hv1])]
        by_cases hc2 : c2 = '='
        · subst hc2
          obtain ⟨h2, hb2, hbs3⟩ := step_pad hbs2
          rw [hb2, if_pos rfl, if_pos rfl]
          by_cases hc3 : c3 = '='
          · subst hc3
            obtain ⟨h3, hb3, hbs4⟩ := step_pad hbs3
            have hnil := drop_utf8_nil_iff (j := i + 4) hlen hbs4
            simp [hb3, hnil]
          · have hb3ne := (step_not_pad hc3 hbs3).choose_spec
            rw [if_neg (fun hcond => hb3ne hcond.1), if_neg (fun hcond => hc3 hcond.1)]
        · have hb2ne := (step_not_pad hc2 hbs2).choose_spec
          rw [if_neg (fun h61 => hb2ne h61), if_neg hc2]
          cases hv2 : α.ofChar? c2 with
          | none =>
            obtain ⟨h2, hlk2, -⟩ := step_bad hascii hv2 hc2 hbs2
            simp [hlk2]
          | some v2 =>
            obtain ⟨h2, hlk2, -, hbs3⟩ := step_some hascii hv2 hbs2
            simp only [Option.bind_some, hlk2]
            rw [if_neg (by simp [ne_ff_of_some (α := α) hv2])]
            by_cases hc3 : c3 = '='
            · subst hc3
              obtain ⟨h3, hb3, hbs4⟩ := step_pad hbs3
              have hnil := drop_utf8_nil_iff (j := i + 4) hlen hbs4
              rw [hb3, if_pos rfl, if_pos rfl]
              simp [hnil]
            · have hb3ne := (step_not_pad hc3 hbs3).choose_spec
              rw [if_neg (fun h61 => hb3ne h61), if_neg hc3]
              cases hv3 : α.ofChar? c3 with
              | none =>
                obtain ⟨h3, hlk3⟩ := step_none hascii hv3 hbs3
                simp [hlk3]
              | some v3 =>
                obtain ⟨h3, hlk3, -, hbs4⟩ := step_some hascii hv3 hbs3
                simp only [Option.bind_some, hlk3]
                rw [if_neg (by simp [ne_ff_of_some (α := α) hv3])]
                exact decodeGoB_eq rest bs (i + 4) _ hlen hbs4

end ByteDecoder

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

/-- The §4 inverse table, computed once at initialization. -/
private def stdDTable : ByteArray := mkDTable alphabet

/-- Strictly decode a base64 string. Returns `none` if the input is not a
canonical RFC 4648 §4 encoding. -/
def decode? (s : String) : Option ByteArray :=
  decodeGoB stdDTable s.toByteArray 0 ByteArray.empty

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
    decode? s = (decodeList alphabet s.toList).map fun bytes => ByteArray.mk bytes.toArray := by
  show decodeGoB (mkDTable alphabet) s.toByteArray 0 ByteArray.empty = _
  rw [decodeGoB_eq (α := alphabet) ofChar?_ascii s.toList s.toByteArray 0 ByteArray.empty
    (Nat.zero_le _)
    (by rw [List.drop_zero, ← String.toByteArray_ofList, String.ofList_toList])]
  exact decodeGo_empty alphabet s

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
#guard (decode? "ab€c").isNone         -- non-ASCII input is rejected

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

/-- The alphabet accepts only ASCII characters. -/
theorem ofChar?_ascii {c : Char} {v : UInt8} (h : ofChar? c = some v) :
    c.toNat < 128 := by
  unfold ofChar? at h
  split at h
  case isTrue h' => have : c.toNat ≤ 90 := h'.2; omega
  case isFalse =>
    split at h
    case isTrue h' => have : c.toNat ≤ 122 := h'.2; omega
    case isFalse =>
      split at h
      case isTrue h' => have : c.toNat ≤ 57 := h'.2; omega
      case isFalse =>
        split at h
        case isTrue h' => subst h'; decide
        case isFalse =>
          split at h
          case isTrue h' => subst h'; decide
          case isFalse => simp at h

theorem ofChar?_eq_some {c : Char} {v : UInt8} (h : ofChar? c = some v) :
    v < 64 ∧ toChar v = c := by
  -- The accepted characters are ASCII, so `c` is one of 128 characters
  -- and the claim reduces to an exhaustive check.
  have hall := char_all_lt
    (P := fun c => ((ofChar? c).all fun v => v < 64 && toChar v == c) = true)
    (by decide) c (ofChar?_ascii h)
  rw [h] at hall
  simpa using hall

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

/-- The §5 inverse table, computed once at initialization. -/
private def urlDTable : ByteArray := mkDTable alphabet

/-- Strictly decode a base64url string. Returns `none` if the input is not
a canonical RFC 4648 §5 encoding (including if padding is omitted). -/
def decode? (s : String) : Option ByteArray :=
  decodeGoB urlDTable s.toByteArray 0 ByteArray.empty

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
    decode? s = (decodeList alphabet s.toList).map fun bytes => ByteArray.mk bytes.toArray := by
  show decodeGoB (mkDTable alphabet) s.toByteArray 0 ByteArray.empty = _
  rw [decodeGoB_eq (α := alphabet) ofChar?_ascii s.toList s.toByteArray 0 ByteArray.empty
    (Nat.zero_le _)
    (by rw [List.drop_zero, ← String.toByteArray_ofList, String.ofList_toList])]
  exact decodeGo_empty alphabet s

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
