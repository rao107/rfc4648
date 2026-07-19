/-!
# Shared proof utilities

Two kinds of glue that core Lean does not provide:

* `decide`-friendly bridges for universally quantified facts about
  `UInt8` and about ASCII `Char`s (used for the character-map lemmas,
  which `bv_decide` cannot handle because they involve `Char`). There is
  no `Decidable` instance for `∀ v : UInt8, P v` or `∀ c : Char, P c`,
  so we reduce to a bounded quantifier over `Nat`, which
  `Nat.decidableBallLT` makes decidable.

* `ByteArray.toList` lemmas relating it to `Array.toList`, needed to lift
  list-level codec theorems to the `ByteArray`/`String` wrappers.
-/

namespace Rfc4648

/-- Prove `P` for every `UInt8` whose value is below `b` by checking the `b`
instantiations `UInt8.ofNat 0, …, UInt8.ofNat (b-1)`; the hypothesis is
decidable via `Nat.decidableBallLT`, so it can be discharged by `decide`. -/
theorem uint8_all_lt {b : Nat} {P : UInt8 → Prop}
    (h : ∀ n : Nat, n < b → P (UInt8.ofNat n)) :
    ∀ v : UInt8, v.toNat < b → P v := fun v hv => by
  have hp := h v.toNat hv
  rwa [UInt8.ofNat_toNat] at hp

/-- Prove `P` for all 256 `UInt8` values; the hypothesis can be discharged
by `decide`. -/
theorem uint8_all {P : UInt8 → Prop}
    (h : ∀ n : Nat, n < 256 → P (UInt8.ofNat n)) : ∀ v : UInt8, P v :=
  fun v => uint8_all_lt h v v.toNat_lt_size

/-- Prove `P` for every `Char` whose code point is below `b` by checking
the `b` instantiations `Char.ofNat 0, …, Char.ofNat (b-1)`; as in
`uint8_all_lt`, the hypothesis can be discharged by `decide`. The
alphabets accept only ASCII, so with `b = 128` this turns facts about
`ofChar?` into a 128-case check. -/
theorem char_all_lt {b : Nat} {P : Char → Prop}
    (h : ∀ n : Nat, n < b → P (Char.ofNat n)) :
    ∀ c : Char, c.toNat < b → P c := fun c hc => by
  have hp := h c.toNat hc
  rwa [Char.ofNat_toNat] at hp

private theorem byteArray_toList_loop (bs : ByteArray) (i : Nat) (r : List UInt8) :
    ByteArray.toList.loop bs i r = r.reverse ++ bs.data.toList.drop i := by
  fun_induction ByteArray.toList.loop bs i r with
  | case1 i r hlt ih =>
    have hlen : i < bs.data.toList.length := by simpa using hlt
    have hget : bs.get! i = bs.data[i]! := by cases bs; rfl
    rw [ih, List.drop_eq_getElem_cons (i := i) hlen, hget,
      getElem!_pos bs.data i hlt]
    simp
    rfl
  | case2 i r hlt =>
    rw [List.drop_eq_nil_of_le (by simpa using Nat.le_of_not_lt hlt)]
    simp

theorem ByteArray.toList_eq_data_toList (bs : ByteArray) :
    bs.toList = bs.data.toList := by
  rw [ByteArray.toList, byteArray_toList_loop]
  simp

theorem ByteArray.toList_mk (l : List UInt8) :
    (ByteArray.mk l.toArray).toList = l := by
  rw [ByteArray.toList_eq_data_toList]

theorem ByteArray.mk_toList_toArray (bs : ByteArray) :
    ByteArray.mk bs.toList.toArray = bs := by
  rw [ByteArray.toList_eq_data_toList]

theorem ByteArray.length_toList (bs : ByteArray) : bs.toList.length = bs.size := by
  rw [ByteArray.toList_eq_data_toList]
  exact Array.length_toList

theorem ByteArray.size_mk_toArray (l : List UInt8) :
    (ByteArray.mk l.toArray).size = l.length := by
  rw [← ByteArray.length_toList, ByteArray.toList_mk]

/-! ## Implementation-equivalence helpers

Extensionality and `ByteArray`/`String` glue shared by the proofs that
the byte-level codec implementations equal their list-model
specifications. -/

theorem str_ext {a b : String} (h : a.toList = b.toList) : a = b := by
  have hab := congrArg String.ofList h
  rwa [String.ofList_toList, String.ofList_toList] at hab

theorem toList_getElem (data : ByteArray) (j : Nat) (h : j < data.size) :
    data.toList[j]'(by rw [ByteArray.length_toList]; exact h) = data[j] := by
  cases data with
  | mk arr => simp [ByteArray.toList_eq_data_toList]; rfl

theorem drop_cons (data : ByteArray) (i : Nat) (h : i < data.size) :
    data.toList.drop i = data[i] :: data.toList.drop (i + 1) := by
  rw [List.drop_eq_getElem_cons (by rw [ByteArray.length_toList]; exact h),
    toList_getElem data i h]

theorem drop_of_size_le (data : ByteArray) (i : Nat) (h : data.size ≤ i) :
    data.toList.drop i = [] :=
  List.drop_eq_nil_of_le (by rw [ByteArray.length_toList]; exact h)

theorem get!_eq (b : ByteArray) (i : Nat) : b.get! i = b.data[i]! := by
  cases b
  rfl

/-- Indexing the `ByteArray` built from `List.ofFn` returns the
generating function's value. Shared by the per-codec `mkTable_get!`
lemmas about the precomputed alphabet tables. -/
theorem get!_ofFn_toByteArray {n : Nat} (f : Fin n → UInt8) {i : Nat} (h : i < n) :
    (List.ofFn f).toByteArray.get! i = f ⟨i, h⟩ := by
  have hdata : (List.ofFn f).toByteArray.data.toList = List.ofFn f :=
    List.toList_data_toByteArray
  have hsz : (List.ofFn f).toByteArray.data.size = n := by
    rw [← Array.length_toList, hdata, List.length_ofFn]
  rw [get!_eq, getElem!_pos _ _ (by omega), ← Array.getElem_toList,
    List.getElem_of_eq hdata, List.getElem_ofFn]

theorem toByteArray_push_ascii (s : String) (c : Char) (hc : c.utf8Size = 1) :
    (s.push c).toByteArray = s.toByteArray.push c.val.toUInt8 := by
  rw [String.toByteArray_push, List.utf8Encode_singleton,
    String.utf8EncodeChar_eq_singleton hc]
  generalize s.toByteArray = b
  cases b
  apply ByteArray.ext
  refine Array.toList_inj.mp ?_
  simp [-Array.toList_inj, ByteArray.push]

theorem emptyWithCapacity_eq (c : Nat) :
    ByteArray.emptyWithCapacity c = ByteArray.empty :=
  ByteArray.ext rfl

/-! ## UTF-8 byte-level decoding glue

The byte-level decoders read a string's UTF-8 bytes directly. These
lemmas relate the byte at the current position to the character at the
head of the remaining input: an ASCII character is exactly its code
point as one byte, and a non-ASCII character starts with a lead byte
`≥ 0x80`. Together with a 256-entry inverse table that rejects every
byte `≥ 0x80`, a byte-level decoder can track its `List Char`
specification without ever decoding UTF-8. -/

theorem size_toByteArray (l : List UInt8) : l.toByteArray.size = l.length := by
  show l.toByteArray.data.size = l.length
  rw [← Array.length_toList, List.toList_data_toByteArray]

theorem toList_toByteArray (l : List UInt8) : l.toByteArray.toList = l := by
  rw [ByteArray.toList_eq_data_toList, List.toList_data_toByteArray]

theorem toList_append (a b : ByteArray) : (a ++ b).toList = a.toList ++ b.toList := by
  simp [ByteArray.toList_eq_data_toList]

/-- `Char.ofNat` on a code point below the surrogate range. -/
theorem char_toNat_ofNat {n : Nat} (h : n < 0xD800) : (Char.ofNat n).toNat = n := by
  rw [Char.ofNat, dif_pos (Or.inl h)]
  rfl

/-- A character's code point as `Nat`, unfolded so `omega` can use it. -/
private theorem toNat_val (c : Char) : c.val.toNat = c.toNat := rfl

/-- ASCII characters occupy one UTF-8 byte. -/
theorem utf8Size_eq_one {c : Char} (hc : c.toNat < 128) : c.utf8Size = 1 :=
  Char.utf8Size_eq_one_iff.mpr (UInt32.le_iff_toNat_le.mpr (by
    have := toNat_val c
    have : (127 : UInt32).toNat = 127 := rfl
    omega))

/-- The single UTF-8 byte of an ASCII character is its code point. -/
theorem toNat_val_toUInt8 {c : Char} (hc : c.toNat < 128) :
    (c.val.toUInt8).toNat = c.toNat := by
  rw [UInt32.toNat_toUInt8]
  have := toNat_val c
  omega

/-- ASCII characters are determined by their UTF-8 byte. -/
theorem ascii_byte_inj {c d : Char} (hc : c.toNat < 128) (hd : d.toNat < 128)
    (h : c.val.toUInt8 = d.val.toUInt8) : c = d := by
  have : c.toNat = d.toNat := by
    rw [← toNat_val_toUInt8 hc, ← toNat_val_toUInt8 hd, h]
  rw [← Char.ofNat_toNat c, ← Char.ofNat_toNat d, this]

/-- Split off the head byte of the remaining input when the remaining
bytes are known to start with an explicit byte list. -/
theorem drop_utf8_head {b : UInt8} {t : List UInt8} {B : ByteArray}
    {bs : ByteArray} {j : Nat}
    (hbs : bs.toList.drop j = ((b :: t).toByteArray ++ B).toList) :
    ∃ h : j < bs.size, bs[j]'h = b ∧
      bs.toList.drop (j + 1) = t ++ B.toList := by
  rw [toList_append, toList_toByteArray] at hbs
  have hj : j < bs.size := by
    rcases Nat.lt_or_ge j bs.size with h | h
    · exact h
    · rw [drop_of_size_le bs j h] at hbs
      simp at hbs
  rw [drop_cons bs j hj] at hbs
  simp only [List.cons_append, List.cons.injEq] at hbs
  exact ⟨hj, hbs.1, hbs.2⟩

/-- One ASCII character at the head of the remaining input is exactly
one byte, its code point; the input advances one byte per character. -/
theorem drop_utf8_ascii {c : Char} (hc : c.toNat < 128) {l : List Char}
    {bs : ByteArray} {j : Nat}
    (hbs : bs.toList.drop j = ((c :: l).utf8Encode).toList) :
    ∃ h : j < bs.size, bs[j]'h = c.val.toUInt8 ∧
      bs.toList.drop (j + 1) = (l.utf8Encode).toList := by
  rw [List.utf8Encode_cons, List.utf8Encode_singleton,
    String.utf8EncodeChar_eq_singleton (utf8Size_eq_one hc)] at hbs
  obtain ⟨h, hb, hrest⟩ := drop_utf8_head hbs
  exact ⟨h, hb, by rw [hrest]; rfl⟩

section LeadBytes

set_option maxRecDepth 4096

private theorem or_c0_high : ∀ x : UInt8, 128 ≤ (x &&& 0x1f ||| 0xc0).toNat :=
  uint8_all (by decide)

private theorem or_e0_high : ∀ x : UInt8, 128 ≤ (x &&& 0x0f ||| 0xe0).toNat :=
  uint8_all (by decide)

private theorem or_f0_high : ∀ x : UInt8, 128 ≤ (x &&& 0x07 ||| 0xf0).toNat :=
  uint8_all (by decide)

end LeadBytes

/-- A non-ASCII character starts with a lead byte `≥ 0x80`, so a decoder
that rejects such bytes rejects it without reading its full encoding. -/
theorem drop_utf8_high {c : Char} (hc : 128 ≤ c.toNat) {l : List Char}
    {bs : ByteArray} {j : Nat}
    (hbs : bs.toList.drop j = ((c :: l).utf8Encode).toList) :
    ∃ h : j < bs.size, 128 ≤ (bs[j]'h).toNat := by
  rw [List.utf8Encode_cons, List.utf8Encode_singleton] at hbs
  obtain h1 | h2 | h3 | h4 := Char.utf8Size_eq c
  · have := UInt32.le_iff_toNat_le.mp (Char.utf8Size_eq_one_iff.mp h1)
    have := toNat_val c
    have : (127 : UInt32).toNat = 127 := rfl
    omega
  · rw [String.utf8EncodeChar_eq_cons_cons h2] at hbs
    obtain ⟨h, hb, -⟩ := drop_utf8_head hbs
    exact ⟨h, by rw [hb]; exact or_c0_high _⟩
  · rw [String.utf8EncodeChar_eq_cons_cons_cons h3] at hbs
    obtain ⟨h, hb, -⟩ := drop_utf8_head hbs
    exact ⟨h, by rw [hb]; exact or_e0_high _⟩
  · rw [String.utf8EncodeChar_eq_cons_cons_cons_cons h4] at hbs
    obtain ⟨h, hb, -⟩ := drop_utf8_head hbs
    exact ⟨h, by rw [hb]; exact or_f0_high _⟩

/-- The remaining characters are exhausted exactly when the byte
position has reached the end of the input. -/
theorem drop_utf8_nil_iff {l : List Char} {bs : ByteArray} {j : Nat}
    (hj : j ≤ bs.size)
    (hbs : bs.toList.drop j = (l.utf8Encode).toList) : j = bs.size ↔ l = [] := by
  constructor
  · intro h
    subst h
    rw [drop_of_size_le bs _ Nat.le.refl] at hbs
    refine List.utf8Encode_eq_empty.mp (ByteArray.ext ?_)
    have : l.utf8Encode.data.toList = [] := by
      rw [← ByteArray.toList_eq_data_toList, ← hbs]
    simpa using this
  · intro h
    subst h
    rw [List.utf8Encode_nil, ByteArray.toList_empty] at hbs
    have := congrArg List.length hbs
    rw [List.length_drop, ByteArray.length_toList] at this
    simp at this
    omega

/-- Every character is at least one byte, so the remaining input has at
least as many bytes as characters. -/
theorem length_le_size_utf8Encode (l : List Char) : l.length ≤ (l.utf8Encode).size := by
  induction l with
  | nil => simp [List.utf8Encode_nil]
  | cons c t ih =>
    rw [List.utf8Encode_cons, ByteArray.size_append, List.utf8Encode_singleton,
      size_toByteArray, String.length_utf8EncodeChar]
    have := c.utf8Size_pos
    simp only [List.length_cons]
    omega

end Rfc4648
