import Std.Tactic.BVDecide
import Rfc4648.Util
import Rfc4648.Alphabet

/-!
# RFC 4648 §8 — Base 16 Encoding

Encoder and strict decoder for base16 (hexadecimal).

Base16 is the degenerate case of the RFC 4648 family: each byte maps to
exactly two characters (4 bits each), so no padding is ever involved.

The codec is parameterized over an `Alphabet 16`; §8 defines only one
alphabet, `Base16.alphabet`. The decoder is strict: it accepts exactly
the outputs of the encoder (uppercase digits only, even length), per the
RFC 4648 §12 security considerations on canonical encodings.

The specification `encodeList` / `decodeList` operates on `List UInt8` /
`List Char`; all theorems are proved against it. The user-facing `encode`
and `decode?` are byte-level implementations over `ByteArray` and
`String` — the encoder writes table-driven UTF-8 bytes into a
preallocated buffer, the decoder reads the string's UTF-8 bytes through
a 256-entry inverse table — each proved equal to the specification
(`encode_eq_model`, `decode?_eq_model`), so every theorem transfers to
them.
-/

namespace Rfc4648.Base16

/-! ## The §8 alphabet -/

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

section CharLemmas

set_option maxRecDepth 4096

theorem ofChar?_toChar : ∀ v : UInt8, v < 16 → ofChar? (toChar v) = some v :=
  uint8_all (by decide)

theorem toChar_ne_pad : ∀ v : UInt8, v < 16 → toChar v ≠ '=' :=
  uint8_all (by decide)

/-- The alphabet accepts only ASCII characters. -/
theorem ofChar?_ascii {c : Char} {v : UInt8} (h : ofChar? c = some v) :
    c.toNat < 128 := by
  unfold ofChar? at h
  split at h
  case isTrue h' => have : c.toNat ≤ 57 := h'.2; omega
  case isFalse =>
    split at h
    case isTrue h' => have : c.toNat ≤ 70 := h'.2; omega
    case isFalse => simp at h

theorem ofChar?_eq_some {c : Char} {v : UInt8} (h : ofChar? c = some v) :
    v < 16 ∧ toChar v = c := by
  -- The accepted characters are ASCII, so `c` is one of 128 characters
  -- and the claim reduces to an exhaustive check.
  have hall := char_all_lt
    (P := fun c => ((ofChar? c).all fun v => v < 16 && toChar v == c) = true)
    (by decide) c (ofChar?_ascii h)
  rw [h] at hall
  simpa using hall

end CharLemmas

/-- The base16 alphabet of RFC 4648 §8 (Table 5). -/
def alphabet : Alphabet 16 where
  toChar := toChar
  ofChar? := ofChar?
  ofChar?_toChar := ofChar?_toChar
  toChar_ne_pad := toChar_ne_pad
  ofChar?_eq_some := ofChar?_eq_some

/-! ## The specification, parameterized over the alphabet -/

/-- Encode bytes as base16 characters: each byte becomes two characters,
high nibble first (RFC 4648 §8). -/
def encodeList (α : Alphabet 16) : List UInt8 → List Char
  | [] => []
  | b :: rest => α.toChar (b >>> 4) :: α.toChar (b &&& 0x0F) :: encodeList α rest

/-- Strictly decode base16 characters, one character pair per byte.
Returns `none` if the length is odd or any character is outside the
alphabet. -/
def decodeList (α : Alphabet 16) : List Char → Option (List UInt8)
  | [] => some []
  | c0 :: c1 :: rest => do
    let v0 ← α.ofChar? c0
    let v1 ← α.ofChar? c1
    let tail ← decodeList α rest
    some (((v0 <<< 4) ||| v1) :: tail)
  | _ => none

/-! ## Bounds on the 4-bit values produced by the encoder

These feed the alphabet lemmas and the byte-level table lookups. -/

private theorem hi_lt (b : UInt8) : b >>> 4 < 16 := by bv_decide

private theorem lo_lt (b : UInt8) : b &&& 0x0F < 16 := by bv_decide

/-! ## The implementation

As in `Rfc4648.Base64`: the list-level codec is the specification only,
and the implementations below are byte-level — the encoder writes
precomputed UTF-8 bytes into a preallocated buffer, the decoder reads
input bytes through the inverse table — each proved equal to the
specification through character-level intermediate models. -/

/-- Tail-recursive base16 encoder: reads bytes directly from `data`
starting at `i`, pushing two characters each onto `acc`. Reference
implementation for the byte-level encoder `encodeGoB`; its output being a
`String` discharges the latter's UTF-8 validity obligation. -/
private def encodeGo (α : Alphabet 16) (data : ByteArray) (i : Nat) (acc : String) : String :=
  if h : i < data.size then
    encodeGo α data (i + 1) <| (acc.push
      (α.toChar (data[i] >>> 4))).push
      (α.toChar (data[i] &&& 0x0F))
  else acc
termination_by data.size - i

/-- String-level base16 encoder without intermediate lists. Equal to
`String.ofList (encodeList α data.toList)` by `encodeFast_eq_model`. -/
private def encodeFast (α : Alphabet 16) (data : ByteArray) : String :=
  encodeGo α data 0 ""

/-- Character-level base16 decoder: consumes character pairs, pushing
decoded bytes onto `acc`. Intermediate model between the specification
`decodeList` and the byte-level decoder `decodeGoB`. -/
private def decodeGo (α : Alphabet 16) : List Char → ByteArray → Option ByteArray
  | [], acc => some acc
  | c0 :: c1 :: rest, acc => do
    let v0 ← α.ofChar? c0
    let v1 ← α.ofChar? c1
    decodeGo α rest (acc.push ((v0 <<< 4) ||| v1))
  | _, _ => none

/-! ### Equivalence with the list model -/

section Model

private theorem encodeGo_eq (α : Alphabet 16) (data : ByteArray) (i : Nat) (acc : String) :
    encodeGo α data i acc = acc ++ String.ofList (encodeList α (data.toList.drop i)) := by
  fun_induction encodeGo α data i acc with
  | case1 i acc h ih =>
    rw [ih, drop_cons data i h]
    apply str_ext
    simp [String.toList_append, String.toList_push, encodeList]
  | case2 i acc h =>
    rw [drop_of_size_le data i (by omega)]
    apply str_ext
    simp [encodeList]

/-- The string-level encoder computes exactly the model encoding. -/
private theorem encodeFast_eq_model (α : Alphabet 16) (data : ByteArray) :
    encodeFast α data = String.ofList (encodeList α data.toList) := by
  rw [encodeFast, encodeGo_eq]
  apply str_ext
  simp

private theorem decodeGo_eq (α : Alphabet 16) : ∀ (cs : List Char) (acc : ByteArray),
    decodeGo α cs acc = (decodeList α cs).map fun l => ⟨acc.data ++ l.toArray⟩
  | [], acc => by
    simp only [decodeGo, decodeList, Option.map_some]
    exact congrArg some (ByteArray.ext (by simp))
  | c0 :: c1 :: rest, acc => by
    simp only [decodeGo, decodeList, Option.bind_eq_bind]
    cases α.ofChar? c0 with
    | none => simp
    | some v0 =>
      cases α.ofChar? c1 with
      | none => simp
      | some v1 =>
        simp only [Option.bind_some, decodeGo_eq α rest (acc.push _)]
        cases decodeList α rest with
        | none => simp
        | some tail =>
          simp only [Option.map_some]
          exact congrArg some (ByteArray.ext (by simp [ByteArray.data_push]))
  | [_], _ => by simp [decodeGo, decodeList]

/-- The character-level decoder started on an empty accumulator computes
exactly the specification's decoding. -/
private theorem decodeGo_empty (α : Alphabet 16) (s : String) :
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

/-- Tail-recursive byte-level base16 decoder: reads 2 input bytes per
step from `bs` starting at `i`, looks their 4-bit values up in the
inverse table `dtbl` (`0xFF` = reject), and pushes decoded bytes onto
`acc`. -/
private def decodeGoB (dtbl : ByteArray) (bs : ByteArray) (i : Nat) (acc : ByteArray) :
    Option ByteArray :=
  if h2 : i + 2 ≤ bs.size then
    let v0 := dtbl.get! (bs[i]'(by omega)).toNat
    let v1 := dtbl.get! (bs[i + 1]'(by omega)).toNat
    if v0 = 0xFF ∨ v1 = 0xFF then none
    else decodeGoB dtbl bs (i + 2) (acc.push ((v0 <<< 4) ||| v1))
  else if i = bs.size then some acc else none
termination_by bs.size - i

section ByteDecoder

variable {α : Alphabet 16}
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
    · by_cases h2 : i + 2 ≤ bs.size
      · rw [decodeGoB.eq_def, dif_pos h2]
        cases hv0 : α.ofChar? c0 with
        | some v0 =>
          obtain ⟨h0, -, -, hbs1⟩ := step_some hascii hv0 hbs
          have := (drop_utf8_nil_iff (j := i + 1) h0 hbs1).mpr rfl
          exact absurd h2 (by omega)
        | none =>
          obtain ⟨h0, hlk0⟩ := step_none hascii hv0 hbs
          simp [hlk0]
      · have hne : i ≠ bs.size := fun h =>
          absurd ((drop_utf8_nil_iff hi hbs).mp h) (by simp)
        rw [decodeGoB.eq_def, dif_neg h2, if_neg hne]
  | c0 :: c1 :: rest => by
    intro bs i acc hi hbs
    -- two characters are at least two bytes, so the two-byte branch runs
    have hlen : i + 2 ≤ bs.size := by
      have hl := congrArg List.length hbs
      rw [List.length_drop, ByteArray.length_toList, ByteArray.length_toList] at hl
      have hge := length_le_size_utf8Encode (c0 :: c1 :: rest)
      simp only [List.length_cons] at hge
      omega
    rw [decodeGoB.eq_def, dif_pos hlen]
    cases hv0 : α.ofChar? c0 with
    | none =>
      obtain ⟨h0, hlk0⟩ := step_none hascii hv0 hbs
      simp [hlk0, decodeGo, hv0]
    | some v0 =>
      obtain ⟨h0, hlk0, -, hbs1⟩ := step_some hascii hv0 hbs
      cases hv1 : α.ofChar? c1 with
      | none =>
        obtain ⟨h1, hlk1⟩ := step_none hascii hv1 hbs1
        simp [hlk1, decodeGo, hv0, hv1]
      | some v1 =>
        obtain ⟨h1, hlk1, -, hbs2⟩ := step_some hascii hv1 hbs1
        simp only [decodeGo, hv0, hv1, Option.bind_eq_bind, Option.bind_some,
          hlk0, hlk1]
        rw [if_neg (by
          simp [ne_ff_of_some (α := α) hv0, ne_ff_of_some (α := α) hv1])]
        exact decodeGoB_eq rest bs (i + 2) _ hlen hbs2

end ByteDecoder

/-! ### Byte-level encoder

Same shape as base64's: the alphabet's 16 UTF-8 bytes are precomputed in
a table, raw bytes are pushed onto a `ByteArray`, and the result is
wrapped as a `String` via the *unchecked* runtime constructor, with the
`IsValidUTF8` obligation discharged by the equality with `encodeGo`. -/

/-- The alphabet's characters as their single UTF-8 bytes. -/
private def mkTable (α : Alphabet 16) : ByteArray :=
  (List.ofFn fun i : Fin 16 => (α.toChar (UInt8.ofNat i.val)).val.toUInt8).toByteArray

/-- Byte-level base16 encoder over a precomputed alphabet table. -/
private def encodeGoB (tbl : ByteArray) (data : ByteArray) (i : Nat) (acc : ByteArray) :
    ByteArray :=
  if h : i < data.size then
    encodeGoB tbl data (i + 1) <| (acc.push
      (tbl.get! (data[i] >>> 4).toNat)).push
      (tbl.get! (data[i] &&& 0x0F).toNat)
  else acc
termination_by data.size - i

section ByteModel

private theorem mkTable_get! (α : Alphabet 16) {v : UInt8} (hv : v < 16) :
    (mkTable α).get! v.toNat = (α.toChar v).val.toUInt8 := by
  have h : v.toNat < 16 := hv
  unfold mkTable
  rw [get!_ofFn_toByteArray _ h, UInt8.ofNat_toNat]

private theorem encodeGoB_eq (α : Alphabet 16)
    (h : ∀ v : UInt8, v < 16 → (α.toChar v).utf8Size = 1) (data : ByteArray)
    (i : Nat) (acc : ByteArray) (sacc : String) (hacc : acc = sacc.toByteArray) :
    encodeGoB (mkTable α) data i acc = (encodeGo α data i sacc).toByteArray := by
  revert sacc hacc
  fun_induction encodeGoB (mkTable α) data i acc with
  | case1 i acc hlt ih =>
    intro sacc hacc
    rw [encodeGo.eq_def, dif_pos hlt]
    refine ih _ ?_
    subst hacc
    rw [toByteArray_push_ascii _ _ (h _ (lo_lt _)),
      toByteArray_push_ascii _ _ (h _ (hi_lt _)),
      mkTable_get! α (hi_lt _), mkTable_get! α (lo_lt _)]
  | case2 i acc hlt =>
    intro sacc hacc
    rw [encodeGo.eq_def, dif_neg hlt]
    exact hacc

end ByteModel

/-- Byte-level base16 encoder. The alphabet table is passed in (so
callers can hoist it to a constant computed once), the output buffer is
preallocated at the exact final size, and the `IsValidUTF8` obligation
of the unchecked `String` constructor is discharged via the equality
with the `String`-level encoder — no validation happens at runtime. -/
private def encodeFaster (α : Alphabet 16)
    (h : ∀ v : UInt8, v < 16 → (α.toChar v).utf8Size = 1)
    (tbl : ByteArray) (htbl : tbl = mkTable α) (data : ByteArray) : String :=
  String.ofByteArray
    (encodeGoB tbl data 0 (ByteArray.emptyWithCapacity (2 * data.size)))
    (by
      rw [htbl, emptyWithCapacity_eq,
        encodeGoB_eq α h data 0 ByteArray.empty "" rfl]
      exact (encodeGo α data 0 "").isValidUTF8)

/-- The byte-level encoder computes exactly the model encoding. -/
private theorem encodeFaster_eq_model (α : Alphabet 16)
    (h : ∀ v : UInt8, v < 16 → (α.toChar v).utf8Size = 1)
    (tbl : ByteArray) (htbl : tbl = mkTable α) (data : ByteArray) :
    encodeFaster α h tbl htbl data = String.ofList (encodeList α data.toList) := by
  rw [← encodeFast_eq_model, ← String.toByteArray_inj]
  show encodeGoB tbl data 0 _ = _
  rw [htbl, emptyWithCapacity_eq]
  exact encodeGoB_eq α h data 0 ByteArray.empty "" rfl

/-! ## The user-facing codec -/

section Ascii

set_option maxRecDepth 4096

private theorem alphabet_ascii : ∀ v : UInt8, v < 16 →
    (alphabet.toChar v).utf8Size = 1 :=
  uint8_all (by decide)

end Ascii

/-- The §8 alphabet table, computed once at initialization. -/
private def stdTable : ByteArray := mkTable alphabet

/-- Encode a byte array as a base16 (hex) string (RFC 4648 §8). -/
def encode (data : ByteArray) : String :=
  encodeFaster alphabet alphabet_ascii stdTable rfl data

/-- The §8 inverse table, computed once at initialization. -/
private def stdDTable : ByteArray := mkDTable alphabet

/-- Strictly decode a base16 string. Returns `none` if the input is not a
canonical RFC 4648 §8 encoding. -/
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
#guard (decode? "6€").isNone      -- non-ASCII input is rejected

/-! ## Round-trip and canonicity

`decodeList_encodeList` / `decode?_encode`: decoding an encoding gives back
the input. `encodeList_decodeList` / `encode_decode?`: anything the strict
decoder accepts is the encoding of its output, i.e. the decoder accepts
exactly the canonical encodings. The list-level theorems hold for any
`Alphabet 16`. -/

section RoundTrip

/-- Round-trip: strictly decoding an encoding yields the original bytes. -/
theorem decodeList_encodeList (α : Alphabet 16) : ∀ bs : List UInt8,
    decodeList α (encodeList α bs) = some bs
  | [] => rfl
  | b :: rest => by
    simp only [encodeList, decodeList, α.ofChar?_toChar _ (hi_lt b),
      α.ofChar?_toChar _ (lo_lt b), Option.bind_eq_bind, Option.bind_some,
      decodeList_encodeList α rest]
    have e : ((b >>> 4) <<< 4) ||| (b &&& 0x0F) = b := by bv_decide
    rw [e]

/-- Canonicity: every string the strict decoder accepts is the encoding of
the bytes it returns. -/
theorem encodeList_decodeList (α : Alphabet 16) : ∀ {cs : List Char} {bs : List UInt8},
    decodeList α cs = some bs → encodeList α bs = cs
  | [], _, h => by
    simp only [decodeList, Option.some.injEq] at h
    simp [← h, encodeList]
  | _c0 :: _c1 :: rest, bs, h => by
    simp only [decodeList, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.some.injEq] at h
    obtain ⟨v0, hv0, v1, hv1, tail, htail, hbs⟩ := h
    obtain ⟨hlt0, hc0⟩ := α.ofChar?_eq_some hv0
    obtain ⟨hlt1, hc1⟩ := α.ofChar?_eq_some hv1
    subst hbs
    have e0 : ((v0 <<< 4) ||| v1) >>> 4 = v0 := by bv_decide
    have e1 : ((v0 <<< 4) ||| v1) &&& 0x0F = v1 := by bv_decide
    simp only [encodeList]
    rw [e0, e1, hc0, hc1, encodeList_decodeList α htail]
  | [_], _, h => by simp [decodeList] at h

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

end Rfc4648.Base16
