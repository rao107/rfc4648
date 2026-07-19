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

The specification `encodeList` / `decodeList` operates on `List UInt8` /
`List Char`; all theorems are proved against it. The user-facing `encode`
and `decode?` are byte-level implementations over `ByteArray` and
`String` — the encoder writes table-driven UTF-8 bytes into a
preallocated buffer, the decoder reads the string's UTF-8 bytes through
a 256-entry inverse table — each proved equal to the specification
(`encode_eq_model`, `decode?_eq_model`), so every theorem transfers to
them.
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

/-- The alphabet accepts only ASCII characters. -/
theorem ofChar?_ascii {c : Char} {v : UInt8} (h : ofChar? c = some v) :
    c.toNat < 128 := by
  unfold ofChar? at h
  split at h
  case isTrue h' => have : c.toNat ≤ 90 := h'.2; omega
  case isFalse =>
    split at h
    case isTrue h' => have : c.toNat ≤ 55 := h'.2; omega
    case isFalse => simp at h

theorem ofChar?_eq_some {c : Char} {v : UInt8} (h : ofChar? c = some v) :
    v < 32 ∧ toChar v = c := by
  -- The accepted characters are ASCII, so `c` is one of 128 characters
  -- and the claim reduces to an exhaustive check.
  have hall := char_all_lt
    (P := fun c => ((ofChar? c).all fun v => v < 32 && toChar v == c) = true)
    (by decide) c (ofChar?_ascii h)
  rw [h] at hall
  simpa using hall

end CharLemmas

/-- The base32 alphabet of RFC 4648 §6 (Table 3). -/
def alphabet : Alphabet 32 where
  toChar := toChar
  ofChar? := ofChar?
  ofChar?_toChar := ofChar?_toChar
  toChar_ne_pad := toChar_ne_pad
  ofChar?_eq_some := ofChar?_eq_some

/-! ## The specification, parameterized over the alphabet -/

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

/-! ## Bounds on the 5-bit values produced by the encoder

These feed the alphabet lemmas and the byte-level table lookups. -/

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

/-! ## The implementation

As in `Rfc4648.Base64`: the list-level codec is the specification only,
and the implementations below are byte-level — the encoder writes
precomputed UTF-8 bytes into a preallocated buffer, the decoder reads
input bytes through the inverse table — each proved equal to the
specification through character-level intermediate models. -/

/-- Tail-recursive base32 encoder: reads 5-byte groups directly from
`data` starting at `i`, pushing characters onto `acc`. Reference
implementation for the byte-level encoder `encodeGoB`; its output being a
`String` discharges the latter's UTF-8 validity obligation. -/
private def encodeGo (α : Alphabet 32) (data : ByteArray) (i : Nat) (acc : String) : String :=
  if h5 : i + 5 ≤ data.size then
    encodeGo α data (i + 5) <| (((((((acc.push
      (α.toChar (data[i]'(by omega) >>> 3))).push
      (α.toChar (((data[i]'(by omega) &&& 0x07) <<< 2) ||| (data[i + 1]'(by omega) >>> 6)))).push
      (α.toChar ((data[i + 1]'(by omega) >>> 1) &&& 0x1F))).push
      (α.toChar (((data[i + 1]'(by omega) &&& 0x01) <<< 4) ||| (data[i + 2]'(by omega) >>> 4)))).push
      (α.toChar (((data[i + 2]'(by omega) &&& 0x0F) <<< 1) ||| (data[i + 3]'(by omega) >>> 7)))).push
      (α.toChar ((data[i + 3]'(by omega) >>> 2) &&& 0x1F))).push
      (α.toChar (((data[i + 3]'(by omega) &&& 0x03) <<< 3) ||| (data[i + 4]'(by omega) >>> 5)))).push
      (α.toChar (data[i + 4]'(by omega) &&& 0x1F))
  else if h1 : data.size = i + 1 then
    (((((((acc.push
      (α.toChar (data[i]'(by omega) >>> 3))).push
      (α.toChar ((data[i]'(by omega) &&& 0x07) <<< 2))).push
      '=').push '=').push '=').push '=').push '=').push '='
  else if h2 : data.size = i + 2 then
    (((((((acc.push
      (α.toChar (data[i]'(by omega) >>> 3))).push
      (α.toChar (((data[i]'(by omega) &&& 0x07) <<< 2) ||| (data[i + 1]'(by omega) >>> 6)))).push
      (α.toChar ((data[i + 1]'(by omega) >>> 1) &&& 0x1F))).push
      (α.toChar ((data[i + 1]'(by omega) &&& 0x01) <<< 4))).push
      '=').push '=').push '=').push '='
  else if h3 : data.size = i + 3 then
    (((((((acc.push
      (α.toChar (data[i]'(by omega) >>> 3))).push
      (α.toChar (((data[i]'(by omega) &&& 0x07) <<< 2) ||| (data[i + 1]'(by omega) >>> 6)))).push
      (α.toChar ((data[i + 1]'(by omega) >>> 1) &&& 0x1F))).push
      (α.toChar (((data[i + 1]'(by omega) &&& 0x01) <<< 4) ||| (data[i + 2]'(by omega) >>> 4)))).push
      (α.toChar ((data[i + 2]'(by omega) &&& 0x0F) <<< 1))).push
      '=').push '=').push '='
  else if h4 : data.size = i + 4 then
    (((((((acc.push
      (α.toChar (data[i]'(by omega) >>> 3))).push
      (α.toChar (((data[i]'(by omega) &&& 0x07) <<< 2) ||| (data[i + 1]'(by omega) >>> 6)))).push
      (α.toChar ((data[i + 1]'(by omega) >>> 1) &&& 0x1F))).push
      (α.toChar (((data[i + 1]'(by omega) &&& 0x01) <<< 4) ||| (data[i + 2]'(by omega) >>> 4)))).push
      (α.toChar (((data[i + 2]'(by omega) &&& 0x0F) <<< 1) ||| (data[i + 3]'(by omega) >>> 7)))).push
      (α.toChar ((data[i + 3]'(by omega) >>> 2) &&& 0x1F))).push
      (α.toChar ((data[i + 3]'(by omega) &&& 0x03) <<< 3))).push '='
  else acc
termination_by data.size - i

/-- String-level base32 encoder without intermediate lists. Equal to
`String.ofList (encodeList α data.toList)` by `encodeFast_eq_model`. -/
private def encodeFast (α : Alphabet 32) (data : ByteArray) : String :=
  encodeGo α data 0 ""

/-- Character-level base32 decoder: consumes 8-character groups, pushing
decoded bytes onto `acc`. Intermediate model between the specification
`decodeList` and the byte-level decoder `decodeGoB`. -/
private def decodeGo (α : Alphabet 32) : List Char → ByteArray → Option ByteArray
  | [], acc => some acc
  | c0 :: c1 :: c2 :: c3 :: c4 :: c5 :: c6 :: c7 :: rest, acc => do
    let v0 ← α.ofChar? c0
    let v1 ← α.ofChar? c1
    if c2 = '=' then
      if c3 = '=' ∧ c4 = '=' ∧ c5 = '=' ∧ c6 = '=' ∧ c7 = '=' ∧ rest = [] ∧
          v1 &&& 0x03 = 0 then
        some (acc.push ((v0 <<< 3) ||| (v1 >>> 2)))
      else none
    else do
      let v2 ← α.ofChar? c2
      let v3 ← α.ofChar? c3
      if c4 = '=' then
        if c5 = '=' ∧ c6 = '=' ∧ c7 = '=' ∧ rest = [] ∧ v3 &&& 0x0F = 0 then
          some ((acc.push ((v0 <<< 3) ||| (v1 >>> 2))).push
            ((v1 <<< 6) ||| (v2 <<< 1) ||| (v3 >>> 4)))
        else none
      else do
        let v4 ← α.ofChar? c4
        if c5 = '=' then
          if c6 = '=' ∧ c7 = '=' ∧ rest = [] ∧ v4 &&& 0x01 = 0 then
            some (((acc.push ((v0 <<< 3) ||| (v1 >>> 2))).push
              ((v1 <<< 6) ||| (v2 <<< 1) ||| (v3 >>> 4))).push
              ((v3 <<< 4) ||| (v4 >>> 1)))
          else none
        else do
          let v5 ← α.ofChar? c5
          let v6 ← α.ofChar? c6
          if c7 = '=' then
            if rest = [] ∧ v6 &&& 0x07 = 0 then
              some ((((acc.push ((v0 <<< 3) ||| (v1 >>> 2))).push
                ((v1 <<< 6) ||| (v2 <<< 1) ||| (v3 >>> 4))).push
                ((v3 <<< 4) ||| (v4 >>> 1))).push
                ((v4 <<< 7) ||| (v5 <<< 2) ||| (v6 >>> 3)))
            else none
          else do
            let v7 ← α.ofChar? c7
            decodeGo α rest <| ((((acc.push
              ((v0 <<< 3) ||| (v1 >>> 2))).push
              ((v1 <<< 6) ||| (v2 <<< 1) ||| (v3 >>> 4))).push
              ((v3 <<< 4) ||| (v4 >>> 1))).push
              ((v4 <<< 7) ||| (v5 <<< 2) ||| (v6 >>> 3))).push
              ((v6 <<< 5) ||| v7)
  | _, _ => none


/-! ### Equivalence with the list model -/

section Model

private theorem drop_two (data : ByteArray) (i : Nat) (h : i + 2 ≤ data.size) :
    data.toList.drop i =
      data[i]'(by omega) :: data[i + 1]'(by omega) :: data.toList.drop (i + 2) := by
  rw [drop_cons data i (by omega), drop_cons data (i + 1) (by omega)]

private theorem drop_three (data : ByteArray) (i : Nat) (h : i + 3 ≤ data.size) :
    data.toList.drop i =
      data[i]'(by omega) :: data[i + 1]'(by omega) :: data[i + 2]'(by omega) ::
        data.toList.drop (i + 3) := by
  rw [drop_two data i (by omega), drop_cons data (i + 2) (by omega)]

private theorem drop_four (data : ByteArray) (i : Nat) (h : i + 4 ≤ data.size) :
    data.toList.drop i =
      data[i]'(by omega) :: data[i + 1]'(by omega) :: data[i + 2]'(by omega) ::
        data[i + 3]'(by omega) :: data.toList.drop (i + 4) := by
  rw [drop_three data i (by omega), drop_cons data (i + 3) (by omega)]

private theorem drop_five (data : ByteArray) (i : Nat) (h : i + 5 ≤ data.size) :
    data.toList.drop i =
      data[i]'(by omega) :: data[i + 1]'(by omega) :: data[i + 2]'(by omega) ::
        data[i + 3]'(by omega) :: data[i + 4]'(by omega) :: data.toList.drop (i + 5) := by
  rw [drop_four data i (by omega), drop_cons data (i + 4) (by omega)]

private theorem encodeGo_eq (α : Alphabet 32) (data : ByteArray) (i : Nat) (acc : String) :
    encodeGo α data i acc = acc ++ String.ofList (encodeList α (data.toList.drop i)) := by
  fun_induction encodeGo α data i acc with
  | case1 i acc h5 ih =>
    rw [ih, drop_five data i (by omega)]
    apply str_ext
    simp [String.toList_append, String.toList_push, encodeList]
  | case2 i acc h5 h1 =>
    rw [drop_cons data i (by omega), drop_of_size_le data (i + 1) (by omega)]
    apply str_ext
    simp [String.toList_append, String.toList_push, encodeList]
  | case3 i acc h5 h1 h2 =>
    rw [drop_two data i (by omega), drop_of_size_le data (i + 2) (by omega)]
    apply str_ext
    simp [String.toList_append, String.toList_push, encodeList]
  | case4 i acc h5 h1 h2 h3 =>
    rw [drop_three data i (by omega), drop_of_size_le data (i + 3) (by omega)]
    apply str_ext
    simp [String.toList_append, String.toList_push, encodeList]
  | case5 i acc h5 h1 h2 h3 h4 =>
    rw [drop_four data i (by omega), drop_of_size_le data (i + 4) (by omega)]
    apply str_ext
    simp [String.toList_append, String.toList_push, encodeList]
  | case6 i acc h5 h1 h2 h3 h4 =>
    rw [drop_of_size_le data i (by omega)]
    apply str_ext
    simp [encodeList]

/-- The string-level encoder computes exactly the model encoding. -/
private theorem encodeFast_eq_model (α : Alphabet 32) (data : ByteArray) :
    encodeFast α data = String.ofList (encodeList α data.toList) := by
  rw [encodeFast, encodeGo_eq]
  apply str_ext
  simp

private theorem decodeGo_eq (α : Alphabet 32) : ∀ (cs : List Char) (acc : ByteArray),
    decodeGo α cs acc = (decodeList α cs).map fun l => ⟨acc.data ++ l.toArray⟩
  | [], acc => by
    simp only [decodeGo, decodeList, Option.map_some]
    exact congrArg some (ByteArray.ext (by simp))
  | c0 :: c1 :: c2 :: c3 :: c4 :: c5 :: c6 :: c7 :: rest, acc => by
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
            cases α.ofChar? c3 with
            | none => simp
            | some v3 =>
              simp only [Option.bind_some]
              split
              · split
                · exact congrArg some (ByteArray.ext (by
                    simp [ByteArray.data_push, ← Array.toList_inj]))
                · simp
              · cases α.ofChar? c4 with
                | none => simp
                | some v4 =>
                  simp only [Option.bind_some]
                  split
                  · split
                    · exact congrArg some (ByteArray.ext (by
                        simp [ByteArray.data_push, ← Array.toList_inj]))
                    · simp
                  · cases α.ofChar? c5 with
                    | none => simp
                    | some v5 =>
                      simp only [Option.bind_some]
                      cases α.ofChar? c6 with
                      | none => simp
                      | some v6 =>
                        simp only [Option.bind_some]
                        split
                        · split
                          · exact congrArg some (ByteArray.ext (by
                              simp [ByteArray.data_push, ← Array.toList_inj]))
                          · simp
                        · cases α.ofChar? c7 with
                          | none => simp
                          | some v7 =>
                            simp only [Option.bind_some, decodeGo_eq α rest
                              (((((acc.push _).push _).push _).push _).push _)]
                            cases decodeList α rest with
                            | none => simp
                            | some tail =>
                              simp only [Option.map_some]
                              exact congrArg some (ByteArray.ext (by simp [ByteArray.data_push]))
  | [_], _ => by simp [decodeGo, decodeList]
  | [_, _], _ => by simp [decodeGo, decodeList]
  | [_, _, _], _ => by simp [decodeGo, decodeList]
  | [_, _, _, _], _ => by simp [decodeGo, decodeList]
  | [_, _, _, _, _], _ => by simp [decodeGo, decodeList]
  | [_, _, _, _, _, _], _ => by simp [decodeGo, decodeList]
  | [_, _, _, _, _, _, _], _ => by simp [decodeGo, decodeList]

/-- The character-level decoder started on an empty accumulator computes
exactly the specification's decoding. -/
private theorem decodeGo_empty (α : Alphabet 32) (s : String) :
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

As in `Rfc4648.Base64`: `decodeGoB` reads the string's UTF-8 bytes
directly through the 256-entry inverse table `mkDTable` (`0xFF` marks
non-alphabet bytes) and never decodes UTF-8 — the step lemmas in
`Rfc4648.Alphabet` show accepted bytes correspond one-to-one to the
characters of the specification. -/

/-- Tail-recursive byte-level base32 decoder: reads 8 input bytes per
step from `bs` starting at `i`, looks their 5-bit values up in the
inverse table `dtbl` (`0xFF` = reject), and pushes decoded bytes onto
`acc`. `61` is `'='`. -/
private def decodeGoB (dtbl : ByteArray) (bs : ByteArray) (i : Nat) (acc : ByteArray) :
    Option ByteArray :=
  if h8 : i + 8 ≤ bs.size then
    let v0 := dtbl.get! (bs[i]'(by omega)).toNat
    let v1 := dtbl.get! (bs[i + 1]'(by omega)).toNat
    if v0 = 0xFF ∨ v1 = 0xFF then none
    else if bs[i + 2]'(by omega) = 61 then
      if bs[i + 3]'(by omega) = 61 ∧ bs[i + 4]'(by omega) = 61 ∧
          bs[i + 5]'(by omega) = 61 ∧ bs[i + 6]'(by omega) = 61 ∧
          bs[i + 7]'(by omega) = 61 ∧ i + 8 = bs.size ∧ v1 &&& 0x03 = 0 then
        some (acc.push ((v0 <<< 3) ||| (v1 >>> 2)))
      else none
    else
      let v2 := dtbl.get! (bs[i + 2]'(by omega)).toNat
      let v3 := dtbl.get! (bs[i + 3]'(by omega)).toNat
      if v2 = 0xFF ∨ v3 = 0xFF then none
      else if bs[i + 4]'(by omega) = 61 then
        if bs[i + 5]'(by omega) = 61 ∧ bs[i + 6]'(by omega) = 61 ∧
            bs[i + 7]'(by omega) = 61 ∧ i + 8 = bs.size ∧ v3 &&& 0x0F = 0 then
          some ((acc.push ((v0 <<< 3) ||| (v1 >>> 2))).push
            ((v1 <<< 6) ||| (v2 <<< 1) ||| (v3 >>> 4)))
        else none
      else
        let v4 := dtbl.get! (bs[i + 4]'(by omega)).toNat
        if v4 = 0xFF then none
        else if bs[i + 5]'(by omega) = 61 then
          if bs[i + 6]'(by omega) = 61 ∧ bs[i + 7]'(by omega) = 61 ∧
              i + 8 = bs.size ∧ v4 &&& 0x01 = 0 then
            some (((acc.push ((v0 <<< 3) ||| (v1 >>> 2))).push
              ((v1 <<< 6) ||| (v2 <<< 1) ||| (v3 >>> 4))).push
              ((v3 <<< 4) ||| (v4 >>> 1)))
          else none
        else
          let v5 := dtbl.get! (bs[i + 5]'(by omega)).toNat
          let v6 := dtbl.get! (bs[i + 6]'(by omega)).toNat
          if v5 = 0xFF ∨ v6 = 0xFF then none
          else if bs[i + 7]'(by omega) = 61 then
            if i + 8 = bs.size ∧ v6 &&& 0x07 = 0 then
              some ((((acc.push ((v0 <<< 3) ||| (v1 >>> 2))).push
                ((v1 <<< 6) ||| (v2 <<< 1) ||| (v3 >>> 4))).push
                ((v3 <<< 4) ||| (v4 >>> 1))).push
                ((v4 <<< 7) ||| (v5 <<< 2) ||| (v6 >>> 3)))
            else none
          else
            let v7 := dtbl.get! (bs[i + 7]'(by omega)).toNat
            if v7 = 0xFF then none
            else
              decodeGoB dtbl bs (i + 8) <| ((((acc.push
                ((v0 <<< 3) ||| (v1 >>> 2))).push
                ((v1 <<< 6) ||| (v2 <<< 1) ||| (v3 >>> 4))).push
                ((v3 <<< 4) ||| (v4 >>> 1))).push
                ((v4 <<< 7) ||| (v5 <<< 2) ||| (v6 >>> 3))).push
                ((v6 <<< 5) ||| v7)
  else if i = bs.size then some acc else none
termination_by bs.size - i

section ByteDecoder

variable {α : Alphabet 32}
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
    · by_cases h8 : i + 8 ≤ bs.size
      · rw [decodeGoB.eq_def, dif_pos h8]
        cases hv0 : α.ofChar? c0 with
        | some v0 =>
          obtain ⟨h0, -, -, hbs1⟩ := step_some hascii hv0 hbs
          have := (drop_utf8_nil_iff (j := i + 1) h0 hbs1).mpr rfl
          exact absurd h8 (by omega)
        | none =>
          obtain ⟨h0, hlk0⟩ := step_none hascii hv0 hbs
          simp [hlk0]
      · have hne : i ≠ bs.size := fun h =>
          absurd ((drop_utf8_nil_iff hi hbs).mp h) (by simp)
        rw [decodeGoB.eq_def, dif_neg h8, if_neg hne]
  | [c0, c1] => by
    intro bs i acc hi hbs
    rw [show decodeGo α [c0, c1] acc = none from by simp [decodeGo]]
    · by_cases h8 : i + 8 ≤ bs.size
      · rw [decodeGoB.eq_def, dif_pos h8]
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
            exact absurd h8 (by omega)
      · have hne : i ≠ bs.size := fun h =>
          absurd ((drop_utf8_nil_iff hi hbs).mp h) (by simp)
        rw [decodeGoB.eq_def, dif_neg h8, if_neg hne]
  | [c0, c1, c2] => by
    intro bs i acc hi hbs
    rw [show decodeGo α [c0, c1, c2] acc = none from by simp [decodeGo]]
    · by_cases h8 : i + 8 ≤ bs.size
      · rw [decodeGoB.eq_def, dif_pos h8]
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
              exact absurd h8 (by omega)
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
                exact absurd h8 (by omega)
      · have hne : i ≠ bs.size := fun h =>
          absurd ((drop_utf8_nil_iff hi hbs).mp h) (by simp)
        rw [decodeGoB.eq_def, dif_neg h8, if_neg hne]
  | [c0, c1, c2, c3] => by
    intro bs i acc hi hbs
    rw [show decodeGo α [c0, c1, c2, c3] acc = none from by simp [decodeGo]]
    · by_cases h8 : i + 8 ≤ bs.size
      · rw [decodeGoB.eq_def, dif_pos h8]
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
            simp only [hlk0, hlk1]
            rw [if_neg (by
              simp [ne_ff_of_some (α := α) hv0, ne_ff_of_some (α := α) hv1])]
            by_cases hc2 : c2 = '='
            · subst hc2
              obtain ⟨h2, hb2, hbs3⟩ := step_pad hbs2
              rw [hb2, if_pos rfl]
              by_cases hc3 : c3 = '='
              · subst hc3
                obtain ⟨h3, -, hbs4⟩ := step_pad hbs3
                have := (drop_utf8_nil_iff (j := i + 4) h3 hbs4).mpr rfl
                exact absurd h8 (by omega)
              · have hb3ne := (step_not_pad hc3 hbs3).choose_spec
                rw [if_neg (fun h => hb3ne h.1)]
            · have hb2ne := (step_not_pad hc2 hbs2).choose_spec
              rw [if_neg (fun h61 => hb2ne h61)]
              cases hv2 : α.ofChar? c2 with
              | none =>
                obtain ⟨h2, hlk2⟩ := step_none hascii hv2 hbs2
                simp [hlk2]
              | some v2 =>
                obtain ⟨h2, hlk2, -, hbs3⟩ := step_some hascii hv2 hbs2
                cases hv3 : α.ofChar? c3 with
                | none =>
                  obtain ⟨h3, hlk3⟩ := step_none hascii hv3 hbs3
                  simp [hlk3]
                | some v3 =>
                  obtain ⟨h3, -, -, hbs4⟩ := step_some hascii hv3 hbs3
                  have := (drop_utf8_nil_iff (j := i + 4) h3 hbs4).mpr rfl
                  exact absurd h8 (by omega)
      · have hne : i ≠ bs.size := fun h =>
          absurd ((drop_utf8_nil_iff hi hbs).mp h) (by simp)
        rw [decodeGoB.eq_def, dif_neg h8, if_neg hne]
  | [c0, c1, c2, c3, c4] => by
    intro bs i acc hi hbs
    rw [show decodeGo α [c0, c1, c2, c3, c4] acc = none from by simp [decodeGo]]
    · by_cases h8 : i + 8 ≤ bs.size
      · rw [decodeGoB.eq_def, dif_pos h8]
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
            simp only [hlk0, hlk1]
            rw [if_neg (by
              simp [ne_ff_of_some (α := α) hv0, ne_ff_of_some (α := α) hv1])]
            by_cases hc2 : c2 = '='
            · subst hc2
              obtain ⟨h2, hb2, hbs3⟩ := step_pad hbs2
              rw [hb2, if_pos rfl]
              by_cases hc3 : c3 = '='
              · subst hc3
                obtain ⟨h3, hb3, hbs4⟩ := step_pad hbs3
                by_cases hc4 : c4 = '='
                · subst hc4
                  obtain ⟨h4, -, hbs5⟩ := step_pad hbs4
                  have := (drop_utf8_nil_iff (j := i + 5) h4 hbs5).mpr rfl
                  exact absurd h8 (by omega)
                · have hb4ne := (step_not_pad hc4 hbs4).choose_spec
                  rw [if_neg (fun h => hb4ne h.2.1)]
              · have hb3ne := (step_not_pad hc3 hbs3).choose_spec
                rw [if_neg (fun h => hb3ne h.1)]
            · have hb2ne := (step_not_pad hc2 hbs2).choose_spec
              rw [if_neg (fun h61 => hb2ne h61)]
              cases hv2 : α.ofChar? c2 with
              | none =>
                obtain ⟨h2, hlk2⟩ := step_none hascii hv2 hbs2
                simp [hlk2]
              | some v2 =>
                obtain ⟨h2, hlk2, -, hbs3⟩ := step_some hascii hv2 hbs2
                cases hv3 : α.ofChar? c3 with
                | none =>
                  obtain ⟨h3, hlk3⟩ := step_none hascii hv3 hbs3
                  simp [hlk3]
                | some v3 =>
                  obtain ⟨h3, hlk3, -, hbs4⟩ := step_some hascii hv3 hbs3
                  simp only [hlk2, hlk3]
                  rw [if_neg (by
                    simp [ne_ff_of_some (α := α) hv2, ne_ff_of_some (α := α) hv3])]
                  by_cases hc4 : c4 = '='
                  · subst hc4
                    obtain ⟨h4, -, hbs5⟩ := step_pad hbs4
                    have := (drop_utf8_nil_iff (j := i + 5) h4 hbs5).mpr rfl
                    exact absurd h8 (by omega)
                  · have hb4ne := (step_not_pad hc4 hbs4).choose_spec
                    rw [if_neg (fun h61 => hb4ne h61)]
                    cases hv4 : α.ofChar? c4 with
                    | none =>
                      obtain ⟨h4, hlk4⟩ := step_none hascii hv4 hbs4
                      simp [hlk4]
                    | some v4 =>
                      obtain ⟨h4, -, -, hbs5⟩ := step_some hascii hv4 hbs4
                      have := (drop_utf8_nil_iff (j := i + 5) h4 hbs5).mpr rfl
                      exact absurd h8 (by omega)
      · have hne : i ≠ bs.size := fun h =>
          absurd ((drop_utf8_nil_iff hi hbs).mp h) (by simp)
        rw [decodeGoB.eq_def, dif_neg h8, if_neg hne]
  | [c0, c1, c2, c3, c4, c5] => by
    intro bs i acc hi hbs
    rw [show decodeGo α [c0, c1, c2, c3, c4, c5] acc = none from by simp [decodeGo]]
    · by_cases h8 : i + 8 ≤ bs.size
      · rw [decodeGoB.eq_def, dif_pos h8]
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
            simp only [hlk0, hlk1]
            rw [if_neg (by
              simp [ne_ff_of_some (α := α) hv0, ne_ff_of_some (α := α) hv1])]
            by_cases hc2 : c2 = '='
            · subst hc2
              obtain ⟨h2, hb2, hbs3⟩ := step_pad hbs2
              rw [hb2, if_pos rfl]
              by_cases hc3 : c3 = '='
              · subst hc3
                obtain ⟨h3, hb3, hbs4⟩ := step_pad hbs3
                by_cases hc4 : c4 = '='
                · subst hc4
                  obtain ⟨h4, hb4, hbs5⟩ := step_pad hbs4
                  by_cases hc5 : c5 = '='
                  · subst hc5
                    obtain ⟨h5, -, hbs6⟩ := step_pad hbs5
                    have := (drop_utf8_nil_iff (j := i + 6) h5 hbs6).mpr rfl
                    exact absurd h8 (by omega)
                  · have hb5ne := (step_not_pad hc5 hbs5).choose_spec
                    rw [if_neg (fun h => hb5ne h.2.2.1)]
                · have hb4ne := (step_not_pad hc4 hbs4).choose_spec
                  rw [if_neg (fun h => hb4ne h.2.1)]
              · have hb3ne := (step_not_pad hc3 hbs3).choose_spec
                rw [if_neg (fun h => hb3ne h.1)]
            · have hb2ne := (step_not_pad hc2 hbs2).choose_spec
              rw [if_neg (fun h61 => hb2ne h61)]
              cases hv2 : α.ofChar? c2 with
              | none =>
                obtain ⟨h2, hlk2⟩ := step_none hascii hv2 hbs2
                simp [hlk2]
              | some v2 =>
                obtain ⟨h2, hlk2, -, hbs3⟩ := step_some hascii hv2 hbs2
                cases hv3 : α.ofChar? c3 with
                | none =>
                  obtain ⟨h3, hlk3⟩ := step_none hascii hv3 hbs3
                  simp [hlk3]
                | some v3 =>
                  obtain ⟨h3, hlk3, -, hbs4⟩ := step_some hascii hv3 hbs3
                  simp only [hlk2, hlk3]
                  rw [if_neg (by
                    simp [ne_ff_of_some (α := α) hv2, ne_ff_of_some (α := α) hv3])]
                  by_cases hc4 : c4 = '='
                  · subst hc4
                    obtain ⟨h4, hb4, hbs5⟩ := step_pad hbs4
                    rw [hb4, if_pos rfl]
                    by_cases hc5 : c5 = '='
                    · subst hc5
                      obtain ⟨h5, -, hbs6⟩ := step_pad hbs5
                      have := (drop_utf8_nil_iff (j := i + 6) h5 hbs6).mpr rfl
                      exact absurd h8 (by omega)
                    · have hb5ne := (step_not_pad hc5 hbs5).choose_spec
                      rw [if_neg (fun h => hb5ne h.1)]
                  · have hb4ne := (step_not_pad hc4 hbs4).choose_spec
                    rw [if_neg (fun h61 => hb4ne h61)]
                    cases hv4 : α.ofChar? c4 with
                    | none =>
                      obtain ⟨h4, hlk4⟩ := step_none hascii hv4 hbs4
                      simp [hlk4]
                    | some v4 =>
                      obtain ⟨h4, hlk4, -, hbs5⟩ := step_some hascii hv4 hbs4
                      simp only [hlk4]
                      rw [if_neg (by simp [ne_ff_of_some (α := α) hv4])]
                      by_cases hc5 : c5 = '='
                      · subst hc5
                        obtain ⟨h5, -, hbs6⟩ := step_pad hbs5
                        have := (drop_utf8_nil_iff (j := i + 6) h5 hbs6).mpr rfl
                        exact absurd h8 (by omega)
                      · have hb5ne := (step_not_pad hc5 hbs5).choose_spec
                        rw [if_neg (fun h61 => hb5ne h61)]
                        cases hv5 : α.ofChar? c5 with
                        | none =>
                          obtain ⟨h5, hlk5⟩ := step_none hascii hv5 hbs5
                          simp [hlk5]
                        | some v5 =>
                          obtain ⟨h5, -, -, hbs6⟩ := step_some hascii hv5 hbs5
                          have := (drop_utf8_nil_iff (j := i + 6) h5 hbs6).mpr rfl
                          exact absurd h8 (by omega)
      · have hne : i ≠ bs.size := fun h =>
          absurd ((drop_utf8_nil_iff hi hbs).mp h) (by simp)
        rw [decodeGoB.eq_def, dif_neg h8, if_neg hne]
  | [c0, c1, c2, c3, c4, c5, c6] => by
    intro bs i acc hi hbs
    rw [show decodeGo α [c0, c1, c2, c3, c4, c5, c6] acc = none from by
      simp [decodeGo]]
    · by_cases h8 : i + 8 ≤ bs.size
      · rw [decodeGoB.eq_def, dif_pos h8]
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
            simp only [hlk0, hlk1]
            rw [if_neg (by
              simp [ne_ff_of_some (α := α) hv0, ne_ff_of_some (α := α) hv1])]
            by_cases hc2 : c2 = '='
            · subst hc2
              obtain ⟨h2, hb2, hbs3⟩ := step_pad hbs2
              rw [hb2, if_pos rfl]
              by_cases hc3 : c3 = '='
              · subst hc3
                obtain ⟨h3, hb3, hbs4⟩ := step_pad hbs3
                by_cases hc4 : c4 = '='
                · subst hc4
                  obtain ⟨h4, hb4, hbs5⟩ := step_pad hbs4
                  by_cases hc5 : c5 = '='
                  · subst hc5
                    obtain ⟨h5, hb5, hbs6⟩ := step_pad hbs5
                    by_cases hc6 : c6 = '='
                    · subst hc6
                      obtain ⟨h6, -, hbs7⟩ := step_pad hbs6
                      have := (drop_utf8_nil_iff (j := i + 7) h6 hbs7).mpr rfl
                      exact absurd h8 (by omega)
                    · have hb6ne := (step_not_pad hc6 hbs6).choose_spec
                      rw [if_neg (fun h => hb6ne h.2.2.2.1)]
                  · have hb5ne := (step_not_pad hc5 hbs5).choose_spec
                    rw [if_neg (fun h => hb5ne h.2.2.1)]
                · have hb4ne := (step_not_pad hc4 hbs4).choose_spec
                  rw [if_neg (fun h => hb4ne h.2.1)]
              · have hb3ne := (step_not_pad hc3 hbs3).choose_spec
                rw [if_neg (fun h => hb3ne h.1)]
            · have hb2ne := (step_not_pad hc2 hbs2).choose_spec
              rw [if_neg (fun h61 => hb2ne h61)]
              cases hv2 : α.ofChar? c2 with
              | none =>
                obtain ⟨h2, hlk2⟩ := step_none hascii hv2 hbs2
                simp [hlk2]
              | some v2 =>
                obtain ⟨h2, hlk2, -, hbs3⟩ := step_some hascii hv2 hbs2
                cases hv3 : α.ofChar? c3 with
                | none =>
                  obtain ⟨h3, hlk3⟩ := step_none hascii hv3 hbs3
                  simp [hlk3]
                | some v3 =>
                  obtain ⟨h3, hlk3, -, hbs4⟩ := step_some hascii hv3 hbs3
                  simp only [hlk2, hlk3]
                  rw [if_neg (by
                    simp [ne_ff_of_some (α := α) hv2, ne_ff_of_some (α := α) hv3])]
                  by_cases hc4 : c4 = '='
                  · subst hc4
                    obtain ⟨h4, hb4, hbs5⟩ := step_pad hbs4
                    rw [hb4, if_pos rfl]
                    by_cases hc5 : c5 = '='
                    · subst hc5
                      obtain ⟨h5, hb5, hbs6⟩ := step_pad hbs5
                      by_cases hc6 : c6 = '='
                      · subst hc6
                        obtain ⟨h6, -, hbs7⟩ := step_pad hbs6
                        have := (drop_utf8_nil_iff (j := i + 7) h6 hbs7).mpr rfl
                        exact absurd h8 (by omega)
                      · have hb6ne := (step_not_pad hc6 hbs6).choose_spec
                        rw [if_neg (fun h => hb6ne h.2.1)]
                    · have hb5ne := (step_not_pad hc5 hbs5).choose_spec
                      rw [if_neg (fun h => hb5ne h.1)]
                  · have hb4ne := (step_not_pad hc4 hbs4).choose_spec
                    rw [if_neg (fun h61 => hb4ne h61)]
                    cases hv4 : α.ofChar? c4 with
                    | none =>
                      obtain ⟨h4, hlk4⟩ := step_none hascii hv4 hbs4
                      simp [hlk4]
                    | some v4 =>
                      obtain ⟨h4, hlk4, -, hbs5⟩ := step_some hascii hv4 hbs4
                      simp only [hlk4]
                      rw [if_neg (by simp [ne_ff_of_some (α := α) hv4])]
                      by_cases hc5 : c5 = '='
                      · subst hc5
                        obtain ⟨h5, hb5, hbs6⟩ := step_pad hbs5
                        rw [hb5, if_pos rfl]
                        by_cases hc6 : c6 = '='
                        · subst hc6
                          obtain ⟨h6, -, hbs7⟩ := step_pad hbs6
                          have := (drop_utf8_nil_iff (j := i + 7) h6 hbs7).mpr rfl
                          exact absurd h8 (by omega)
                        · have hb6ne := (step_not_pad hc6 hbs6).choose_spec
                          rw [if_neg (fun h => hb6ne h.1)]
                      · have hb5ne := (step_not_pad hc5 hbs5).choose_spec
                        rw [if_neg (fun h61 => hb5ne h61)]
                        cases hv5 : α.ofChar? c5 with
                        | none =>
                          obtain ⟨h5, hlk5⟩ := step_none hascii hv5 hbs5
                          simp [hlk5]
                        | some v5 =>
                          obtain ⟨h5, hlk5, -, hbs6⟩ := step_some hascii hv5 hbs5
                          cases hv6 : α.ofChar? c6 with
                          | none =>
                            obtain ⟨h6, hlk6⟩ := step_none hascii hv6 hbs6
                            simp [hlk6]
                          | some v6 =>
                            obtain ⟨h6, -, -, hbs7⟩ := step_some hascii hv6 hbs6
                            have := (drop_utf8_nil_iff (j := i + 7) h6 hbs7).mpr rfl
                            exact absurd h8 (by omega)
      · have hne : i ≠ bs.size := fun h =>
          absurd ((drop_utf8_nil_iff hi hbs).mp h) (by simp)
        rw [decodeGoB.eq_def, dif_neg h8, if_neg hne]
  | c0 :: c1 :: c2 :: c3 :: c4 :: c5 :: c6 :: c7 :: rest => by
    intro bs i acc hi hbs
    -- eight characters are at least eight bytes, so the eight-byte branch runs
    have hlen : i + 8 ≤ bs.size := by
      have hl := congrArg List.length hbs
      rw [List.length_drop, ByteArray.length_toList, ByteArray.length_toList] at hl
      have hge := length_le_size_utf8Encode
        (c0 :: c1 :: c2 :: c3 :: c4 :: c5 :: c6 :: c7 :: rest)
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
        · -- "xx======": pad from position 2
          subst hc2
          obtain ⟨h2, hb2, hbs3⟩ := step_pad hbs2
          rw [hb2, if_pos rfl, if_pos rfl]
          by_cases hc3 : c3 = '='
          · subst hc3
            obtain ⟨h3, hb3, hbs4⟩ := step_pad hbs3
            by_cases hc4 : c4 = '='
            · subst hc4
              obtain ⟨h4, hb4, hbs5⟩ := step_pad hbs4
              by_cases hc5 : c5 = '='
              · subst hc5
                obtain ⟨h5, hb5, hbs6⟩ := step_pad hbs5
                by_cases hc6 : c6 = '='
                · subst hc6
                  obtain ⟨h6, hb6, hbs7⟩ := step_pad hbs6
                  by_cases hc7 : c7 = '='
                  · subst hc7
                    obtain ⟨h7, hb7, hbs8⟩ := step_pad hbs7
                    have hnil := drop_utf8_nil_iff (j := i + 8) hlen hbs8
                    simp [hb3, hb4, hb5, hb6, hb7, hnil]
                  · have hb7ne := (step_not_pad hc7 hbs7).choose_spec
                    rw [if_neg (fun h => hb7ne h.2.2.2.2.1),
                      if_neg (fun h => hc7 h.2.2.2.2.1)]
                · have hb6ne := (step_not_pad hc6 hbs6).choose_spec
                  rw [if_neg (fun h => hb6ne h.2.2.2.1),
                    if_neg (fun h => hc6 h.2.2.2.1)]
              · have hb5ne := (step_not_pad hc5 hbs5).choose_spec
                rw [if_neg (fun h => hb5ne h.2.2.1), if_neg (fun h => hc5 h.2.2.1)]
            · have hb4ne := (step_not_pad hc4 hbs4).choose_spec
              rw [if_neg (fun h => hb4ne h.2.1), if_neg (fun h => hc4 h.2.1)]
          · have hb3ne := (step_not_pad hc3 hbs3).choose_spec
            rw [if_neg (fun h => hb3ne h.1), if_neg (fun h => hc3 h.1)]
        · have hb2ne := (step_not_pad hc2 hbs2).choose_spec
          rw [if_neg (fun h61 => hb2ne h61), if_neg hc2]
          cases hv2 : α.ofChar? c2 with
          | none =>
            obtain ⟨h2, hlk2, -⟩ := step_bad hascii hv2 hc2 hbs2
            simp [hlk2]
          | some v2 =>
            obtain ⟨h2, hlk2, -, hbs3⟩ := step_some hascii hv2 hbs2
            cases hv3 : α.ofChar? c3 with
            | none =>
              obtain ⟨h3, hlk3⟩ := step_none hascii hv3 hbs3
              simp [hlk3]
            | some v3 =>
              obtain ⟨h3, hlk3, -, hbs4⟩ := step_some hascii hv3 hbs3
              simp only [Option.bind_some, hlk2, hlk3]
              rw [if_neg (by
                simp [ne_ff_of_some (α := α) hv2, ne_ff_of_some (α := α) hv3])]
              by_cases hc4 : c4 = '='
              · -- "xxxx====": pad from position 4
                subst hc4
                obtain ⟨h4, hb4, hbs5⟩ := step_pad hbs4
                rw [hb4, if_pos rfl, if_pos rfl]
                by_cases hc5 : c5 = '='
                · subst hc5
                  obtain ⟨h5, hb5, hbs6⟩ := step_pad hbs5
                  by_cases hc6 : c6 = '='
                  · subst hc6
                    obtain ⟨h6, hb6, hbs7⟩ := step_pad hbs6
                    by_cases hc7 : c7 = '='
                    · subst hc7
                      obtain ⟨h7, hb7, hbs8⟩ := step_pad hbs7
                      have hnil := drop_utf8_nil_iff (j := i + 8) hlen hbs8
                      simp [hb5, hb6, hb7, hnil]
                    · have hb7ne := (step_not_pad hc7 hbs7).choose_spec
                      rw [if_neg (fun h => hb7ne h.2.2.1),
                        if_neg (fun h => hc7 h.2.2.1)]
                  · have hb6ne := (step_not_pad hc6 hbs6).choose_spec
                    rw [if_neg (fun h => hb6ne h.2.1), if_neg (fun h => hc6 h.2.1)]
                · have hb5ne := (step_not_pad hc5 hbs5).choose_spec
                  rw [if_neg (fun h => hb5ne h.1), if_neg (fun h => hc5 h.1)]
              · have hb4ne := (step_not_pad hc4 hbs4).choose_spec
                rw [if_neg (fun h61 => hb4ne h61), if_neg hc4]
                cases hv4 : α.ofChar? c4 with
                | none =>
                  obtain ⟨h4, hlk4⟩ := step_none hascii hv4 hbs4
                  simp [hlk4]
                | some v4 =>
                  obtain ⟨h4, hlk4, -, hbs5⟩ := step_some hascii hv4 hbs4
                  simp only [Option.bind_some, hlk4]
                  rw [if_neg (by simp [ne_ff_of_some (α := α) hv4])]
                  by_cases hc5 : c5 = '='
                  · -- "xxxxx===": pad from position 5
                    subst hc5
                    obtain ⟨h5, hb5, hbs6⟩ := step_pad hbs5
                    rw [hb5, if_pos rfl, if_pos rfl]
                    by_cases hc6 : c6 = '='
                    · subst hc6
                      obtain ⟨h6, hb6, hbs7⟩ := step_pad hbs6
                      by_cases hc7 : c7 = '='
                      · subst hc7
                        obtain ⟨h7, hb7, hbs8⟩ := step_pad hbs7
                        have hnil := drop_utf8_nil_iff (j := i + 8) hlen hbs8
                        simp [hb6, hb7, hnil]
                      · have hb7ne := (step_not_pad hc7 hbs7).choose_spec
                        rw [if_neg (fun h => hb7ne h.2.1),
                          if_neg (fun h => hc7 h.2.1)]
                    · have hb6ne := (step_not_pad hc6 hbs6).choose_spec
                      rw [if_neg (fun h => hb6ne h.1), if_neg (fun h => hc6 h.1)]
                  · have hb5ne := (step_not_pad hc5 hbs5).choose_spec
                    rw [if_neg (fun h61 => hb5ne h61), if_neg hc5]
                    cases hv5 : α.ofChar? c5 with
                    | none =>
                      obtain ⟨h5, hlk5⟩ := step_none hascii hv5 hbs5
                      simp [hlk5]
                    | some v5 =>
                      obtain ⟨h5, hlk5, -, hbs6⟩ := step_some hascii hv5 hbs5
                      cases hv6 : α.ofChar? c6 with
                      | none =>
                        obtain ⟨h6, hlk6⟩ := step_none hascii hv6 hbs6
                        simp [hlk6]
                      | some v6 =>
                        obtain ⟨h6, hlk6, -, hbs7⟩ := step_some hascii hv6 hbs6
                        simp only [Option.bind_some, hlk5, hlk6]
                        rw [if_neg (by
                          simp [ne_ff_of_some (α := α) hv5,
                            ne_ff_of_some (α := α) hv6])]
                        by_cases hc7 : c7 = '='
                        · -- "xxxxxxx=": pad from position 7
                          subst hc7
                          obtain ⟨h7, hb7, hbs8⟩ := step_pad hbs7
                          rw [hb7, if_pos rfl, if_pos rfl]
                          have hnil := drop_utf8_nil_iff (j := i + 8) hlen hbs8
                          simp [hnil]
                        · have hb7ne := (step_not_pad hc7 hbs7).choose_spec
                          rw [if_neg (fun h61 => hb7ne h61), if_neg hc7]
                          cases hv7 : α.ofChar? c7 with
                          | none =>
                            obtain ⟨h7, hlk7⟩ := step_none hascii hv7 hbs7
                            simp [hlk7]
                          | some v7 =>
                            obtain ⟨h7, hlk7, -, hbs8⟩ := step_some hascii hv7 hbs7
                            simp only [Option.bind_some, hlk7]
                            rw [if_neg (by simp [ne_ff_of_some (α := α) hv7])]
                            exact decodeGoB_eq rest bs (i + 8) _ hlen hbs8

end ByteDecoder

/-! ### Byte-level encoder

Same shape as base64's: the alphabet's 32 UTF-8 bytes are precomputed in
a table, raw bytes are pushed onto a `ByteArray`, and the result is
wrapped as a `String` via the *unchecked* runtime constructor, with the
`IsValidUTF8` obligation discharged by the equality with `encodeGo`. -/

/-- The alphabet's characters as their single UTF-8 bytes. -/
private def mkTable (α : Alphabet 32) : ByteArray :=
  (List.ofFn fun i : Fin 32 => (α.toChar (UInt8.ofNat i.val)).val.toUInt8).toByteArray

/-- Byte-level base32 encoder over a precomputed alphabet table. -/
private def encodeGoB (tbl : ByteArray) (data : ByteArray) (i : Nat) (acc : ByteArray) :
    ByteArray :=
  if h5 : i + 5 ≤ data.size then
    encodeGoB tbl data (i + 5) <| (((((((acc.push
      (tbl.get! (data[i]'(by omega) >>> 3).toNat)).push
      (tbl.get! (((data[i]'(by omega) &&& 0x07) <<< 2) ||| (data[i + 1]'(by omega) >>> 6)).toNat)).push
      (tbl.get! ((data[i + 1]'(by omega) >>> 1) &&& 0x1F).toNat)).push
      (tbl.get! (((data[i + 1]'(by omega) &&& 0x01) <<< 4) ||| (data[i + 2]'(by omega) >>> 4)).toNat)).push
      (tbl.get! (((data[i + 2]'(by omega) &&& 0x0F) <<< 1) ||| (data[i + 3]'(by omega) >>> 7)).toNat)).push
      (tbl.get! ((data[i + 3]'(by omega) >>> 2) &&& 0x1F).toNat)).push
      (tbl.get! (((data[i + 3]'(by omega) &&& 0x03) <<< 3) ||| (data[i + 4]'(by omega) >>> 5)).toNat)).push
      (tbl.get! (data[i + 4]'(by omega) &&& 0x1F).toNat)
  else if h1 : data.size = i + 1 then
    (((((((acc.push
      (tbl.get! (data[i]'(by omega) >>> 3).toNat)).push
      (tbl.get! ((data[i]'(by omega) &&& 0x07) <<< 2).toNat)).push
      '='.val.toUInt8).push '='.val.toUInt8).push '='.val.toUInt8).push
      '='.val.toUInt8).push '='.val.toUInt8).push '='.val.toUInt8
  else if h2 : data.size = i + 2 then
    (((((((acc.push
      (tbl.get! (data[i]'(by omega) >>> 3).toNat)).push
      (tbl.get! (((data[i]'(by omega) &&& 0x07) <<< 2) ||| (data[i + 1]'(by omega) >>> 6)).toNat)).push
      (tbl.get! ((data[i + 1]'(by omega) >>> 1) &&& 0x1F).toNat)).push
      (tbl.get! ((data[i + 1]'(by omega) &&& 0x01) <<< 4).toNat)).push
      '='.val.toUInt8).push '='.val.toUInt8).push '='.val.toUInt8).push '='.val.toUInt8
  else if h3 : data.size = i + 3 then
    (((((((acc.push
      (tbl.get! (data[i]'(by omega) >>> 3).toNat)).push
      (tbl.get! (((data[i]'(by omega) &&& 0x07) <<< 2) ||| (data[i + 1]'(by omega) >>> 6)).toNat)).push
      (tbl.get! ((data[i + 1]'(by omega) >>> 1) &&& 0x1F).toNat)).push
      (tbl.get! (((data[i + 1]'(by omega) &&& 0x01) <<< 4) ||| (data[i + 2]'(by omega) >>> 4)).toNat)).push
      (tbl.get! ((data[i + 2]'(by omega) &&& 0x0F) <<< 1).toNat)).push
      '='.val.toUInt8).push '='.val.toUInt8).push '='.val.toUInt8
  else if h4 : data.size = i + 4 then
    (((((((acc.push
      (tbl.get! (data[i]'(by omega) >>> 3).toNat)).push
      (tbl.get! (((data[i]'(by omega) &&& 0x07) <<< 2) ||| (data[i + 1]'(by omega) >>> 6)).toNat)).push
      (tbl.get! ((data[i + 1]'(by omega) >>> 1) &&& 0x1F).toNat)).push
      (tbl.get! (((data[i + 1]'(by omega) &&& 0x01) <<< 4) ||| (data[i + 2]'(by omega) >>> 4)).toNat)).push
      (tbl.get! (((data[i + 2]'(by omega) &&& 0x0F) <<< 1) ||| (data[i + 3]'(by omega) >>> 7)).toNat)).push
      (tbl.get! ((data[i + 3]'(by omega) >>> 2) &&& 0x1F).toNat)).push
      (tbl.get! ((data[i + 3]'(by omega) &&& 0x03) <<< 3).toNat)).push '='.val.toUInt8
  else acc
termination_by data.size - i

section ByteModel

private theorem mkTable_get! (α : Alphabet 32) {v : UInt8} (hv : v < 32) :
    (mkTable α).get! v.toNat = (α.toChar v).val.toUInt8 := by
  have h : v.toNat < 32 := hv
  unfold mkTable
  rw [get!_ofFn_toByteArray _ h, UInt8.ofNat_toNat]

private theorem encodeGoB_eq (α : Alphabet 32)
    (h : ∀ v : UInt8, v < 32 → (α.toChar v).utf8Size = 1) (data : ByteArray)
    (i : Nat) (acc : ByteArray) (sacc : String) (hacc : acc = sacc.toByteArray) :
    encodeGoB (mkTable α) data i acc = (encodeGo α data i sacc).toByteArray := by
  revert sacc hacc
  fun_induction encodeGoB (mkTable α) data i acc with
  | case1 i acc h5 ih =>
    intro sacc hacc
    rw [encodeGo.eq_def, dif_pos h5]
    refine ih _ ?_
    subst hacc
    rw [toByteArray_push_ascii _ _ (h _ (w7_lt _)),
      toByteArray_push_ascii _ _ (h _ (w6_lt _ _)),
      toByteArray_push_ascii _ _ (h _ (w5_lt _)),
      toByteArray_push_ascii _ _ (h _ (w4_lt _ _)),
      toByteArray_push_ascii _ _ (h _ (w3_lt _ _)),
      toByteArray_push_ascii _ _ (h _ (w2_lt _)),
      toByteArray_push_ascii _ _ (h _ (w1_lt _ _)),
      toByteArray_push_ascii _ _ (h _ (w0_lt _)),
      mkTable_get! α (w0_lt _), mkTable_get! α (w1_lt _ _),
      mkTable_get! α (w2_lt _), mkTable_get! α (w3_lt _ _),
      mkTable_get! α (w4_lt _ _), mkTable_get! α (w5_lt _),
      mkTable_get! α (w6_lt _ _), mkTable_get! α (w7_lt _)]
  | case2 i acc h5 h1 =>
    intro sacc hacc
    rw [encodeGo.eq_def, dif_neg h5, dif_pos h1]
    subst hacc
    rw [toByteArray_push_ascii _ _ (by decide : ('=' : Char).utf8Size = 1),
      toByteArray_push_ascii _ _ (by decide : ('=' : Char).utf8Size = 1),
      toByteArray_push_ascii _ _ (by decide : ('=' : Char).utf8Size = 1),
      toByteArray_push_ascii _ _ (by decide : ('=' : Char).utf8Size = 1),
      toByteArray_push_ascii _ _ (by decide : ('=' : Char).utf8Size = 1),
      toByteArray_push_ascii _ _ (by decide : ('=' : Char).utf8Size = 1),
      toByteArray_push_ascii _ _ (h _ (w1p_lt _)),
      toByteArray_push_ascii _ _ (h _ (w0_lt _)),
      mkTable_get! α (w0_lt _), mkTable_get! α (w1p_lt _)]
  | case3 i acc h5 h1 h2 =>
    intro sacc hacc
    rw [encodeGo.eq_def, dif_neg h5, dif_neg h1, dif_pos h2]
    subst hacc
    rw [toByteArray_push_ascii _ _ (by decide : ('=' : Char).utf8Size = 1),
      toByteArray_push_ascii _ _ (by decide : ('=' : Char).utf8Size = 1),
      toByteArray_push_ascii _ _ (by decide : ('=' : Char).utf8Size = 1),
      toByteArray_push_ascii _ _ (by decide : ('=' : Char).utf8Size = 1),
      toByteArray_push_ascii _ _ (h _ (w3p_lt _)),
      toByteArray_push_ascii _ _ (h _ (w2_lt _)),
      toByteArray_push_ascii _ _ (h _ (w1_lt _ _)),
      toByteArray_push_ascii _ _ (h _ (w0_lt _)),
      mkTable_get! α (w0_lt _), mkTable_get! α (w1_lt _ _),
      mkTable_get! α (w2_lt _), mkTable_get! α (w3p_lt _)]
  | case4 i acc h5 h1 h2 h3 =>
    intro sacc hacc
    rw [encodeGo.eq_def, dif_neg h5, dif_neg h1, dif_neg h2, dif_pos h3]
    subst hacc
    rw [toByteArray_push_ascii _ _ (by decide : ('=' : Char).utf8Size = 1),
      toByteArray_push_ascii _ _ (by decide : ('=' : Char).utf8Size = 1),
      toByteArray_push_ascii _ _ (by decide : ('=' : Char).utf8Size = 1),
      toByteArray_push_ascii _ _ (h _ (w4p_lt _)),
      toByteArray_push_ascii _ _ (h _ (w3_lt _ _)),
      toByteArray_push_ascii _ _ (h _ (w2_lt _)),
      toByteArray_push_ascii _ _ (h _ (w1_lt _ _)),
      toByteArray_push_ascii _ _ (h _ (w0_lt _)),
      mkTable_get! α (w0_lt _), mkTable_get! α (w1_lt _ _),
      mkTable_get! α (w2_lt _), mkTable_get! α (w3_lt _ _),
      mkTable_get! α (w4p_lt _)]
  | case5 i acc h5 h1 h2 h3 h4 =>
    intro sacc hacc
    rw [encodeGo.eq_def, dif_neg h5, dif_neg h1, dif_neg h2, dif_neg h3, dif_pos h4]
    subst hacc
    rw [toByteArray_push_ascii _ _ (by decide : ('=' : Char).utf8Size = 1),
      toByteArray_push_ascii _ _ (h _ (w6p_lt _)),
      toByteArray_push_ascii _ _ (h _ (w5_lt _)),
      toByteArray_push_ascii _ _ (h _ (w4_lt _ _)),
      toByteArray_push_ascii _ _ (h _ (w3_lt _ _)),
      toByteArray_push_ascii _ _ (h _ (w2_lt _)),
      toByteArray_push_ascii _ _ (h _ (w1_lt _ _)),
      toByteArray_push_ascii _ _ (h _ (w0_lt _)),
      mkTable_get! α (w0_lt _), mkTable_get! α (w1_lt _ _),
      mkTable_get! α (w2_lt _), mkTable_get! α (w3_lt _ _),
      mkTable_get! α (w4_lt _ _), mkTable_get! α (w5_lt _),
      mkTable_get! α (w6p_lt _)]
  | case6 i acc h5 h1 h2 h3 h4 =>
    intro sacc hacc
    rw [encodeGo.eq_def, dif_neg h5, dif_neg h1, dif_neg h2, dif_neg h3, dif_neg h4]
    exact hacc

end ByteModel

/-- Byte-level base32 encoder. The alphabet table is passed in (so
callers can hoist it to a constant computed once), the output buffer is
preallocated at the exact final size, and the `IsValidUTF8` obligation
of the unchecked `String` constructor is discharged via the equality
with the `String`-level encoder — no validation happens at runtime. -/
private def encodeFaster (α : Alphabet 32)
    (h : ∀ v : UInt8, v < 32 → (α.toChar v).utf8Size = 1)
    (tbl : ByteArray) (htbl : tbl = mkTable α) (data : ByteArray) : String :=
  String.ofByteArray
    (encodeGoB tbl data 0 (ByteArray.emptyWithCapacity (8 * ((data.size + 4) / 5))))
    (by
      rw [htbl, emptyWithCapacity_eq,
        encodeGoB_eq α h data 0 ByteArray.empty "" rfl]
      exact (encodeGo α data 0 "").isValidUTF8)

/-- The byte-level encoder computes exactly the model encoding. -/
private theorem encodeFaster_eq_model (α : Alphabet 32)
    (h : ∀ v : UInt8, v < 32 → (α.toChar v).utf8Size = 1)
    (tbl : ByteArray) (htbl : tbl = mkTable α) (data : ByteArray) :
    encodeFaster α h tbl htbl data = String.ofList (encodeList α data.toList) := by
  rw [← encodeFast_eq_model, ← String.toByteArray_inj]
  show encodeGoB tbl data 0 _ = _
  rw [htbl, emptyWithCapacity_eq]
  exact encodeGoB_eq α h data 0 ByteArray.empty "" rfl

/-! ## The user-facing codec -/

section Ascii

set_option maxRecDepth 4096

private theorem alphabet_ascii : ∀ v : UInt8, v < 32 →
    (alphabet.toChar v).utf8Size = 1 :=
  uint8_all (by decide)

end Ascii

/-- The §6 alphabet table, computed once at initialization. -/
private def stdTable : ByteArray := mkTable alphabet

/-- Encode a byte array as a base32 string (RFC 4648 §6, with padding). -/
def encode (data : ByteArray) : String :=
  encodeFaster alphabet alphabet_ascii stdTable rfl data

/-- The §6 inverse table, computed once at initialization. -/
private def stdDTable : ByteArray := mkDTable alphabet

/-- Strictly decode a base32 string. Returns `none` if the input is not a
canonical RFC 4648 §6 encoding. -/
def decode? (s : String) : Option ByteArray :=
  decodeGoB stdDTable s.toByteArray 0 ByteArray.empty

/-- `encode` computes exactly the specification `encodeList`; encoder
theorems transfer through this equality. -/
theorem encode_eq_model (data : ByteArray) :
    encode data = String.ofList (encodeList alphabet data.toList) :=
  encodeFaster_eq_model alphabet alphabet_ascii stdTable rfl data

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
#guard (decode? "MZXW€===").isNone          -- non-ASCII input is rejected

/-! ## Round-trip and canonicity

The list-level theorems hold for any `Alphabet 32`. -/

section RoundTrip

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

/-- The alphabet accepts only ASCII characters. -/
theorem ofChar?_ascii {c : Char} {v : UInt8} (h : ofChar? c = some v) :
    c.toNat < 128 := by
  unfold ofChar? at h
  split at h
  case isTrue h' => have : c.toNat ≤ 57 := h'.2; omega
  case isFalse =>
    split at h
    case isTrue h' => have : c.toNat ≤ 86 := h'.2; omega
    case isFalse => simp at h

theorem ofChar?_eq_some {c : Char} {v : UInt8} (h : ofChar? c = some v) :
    v < 32 ∧ toChar v = c := by
  -- The accepted characters are ASCII, so `c` is one of 128 characters
  -- and the claim reduces to an exhaustive check.
  have hall := char_all_lt
    (P := fun c => ((ofChar? c).all fun v => v < 32 && toChar v == c) = true)
    (by decide) c (ofChar?_ascii h)
  rw [h] at hall
  simpa using hall

end CharLemmas

/-- The base32hex alphabet of RFC 4648 §7 (Table 4). -/
def alphabet : Alphabet 32 where
  toChar := toChar
  ofChar? := ofChar?
  ofChar?_toChar := ofChar?_toChar
  toChar_ne_pad := toChar_ne_pad
  ofChar?_eq_some := ofChar?_eq_some

section Ascii

set_option maxRecDepth 4096

private theorem alphabet_ascii : ∀ v : UInt8, v < 32 →
    (alphabet.toChar v).utf8Size = 1 :=
  uint8_all (by decide)

end Ascii

/-- The §7 alphabet table, computed once at initialization. -/
private def hexTable : ByteArray := mkTable alphabet

/-- Encode a byte array as a base32hex string (RFC 4648 §7, with padding). -/
def encode (data : ByteArray) : String :=
  encodeFaster alphabet alphabet_ascii hexTable rfl data

/-- The §7 inverse table, computed once at initialization. -/
private def hexDTable : ByteArray := mkDTable alphabet

/-- Strictly decode a base32hex string. Returns `none` if the input is not
a canonical RFC 4648 §7 encoding. -/
def decode? (s : String) : Option ByteArray :=
  decodeGoB hexDTable s.toByteArray 0 ByteArray.empty

/-- `encode` computes exactly the specification `encodeList`; encoder
theorems transfer through this equality. -/
theorem encode_eq_model (data : ByteArray) :
    encode data = String.ofList (encodeList alphabet data.toList) :=
  encodeFaster_eq_model alphabet alphabet_ascii hexTable rfl data

/-- `decode?` computes exactly the specification `decodeList`; decoder
theorems transfer through this equality. -/
theorem decode?_eq_model (s : String) :
    decode? s = (decodeList alphabet s.toList).map fun bytes => ByteArray.mk bytes.toArray := by
  show decodeGoB (mkDTable alphabet) s.toByteArray 0 ByteArray.empty = _
  rw [decodeGoB_eq (α := alphabet) ofChar?_ascii s.toList s.toByteArray 0 ByteArray.empty
    (Nat.zero_le _)
    (by rw [List.drop_zero, ← String.toByteArray_ofList, String.ofList_toList])]
  exact decodeGo_empty alphabet s

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
#guard (decode? "C€======").isNone   -- non-ASCII input is rejected

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

end Hex

end Rfc4648.Base32
