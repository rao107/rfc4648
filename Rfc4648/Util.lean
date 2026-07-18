/-!
# Shared proof utilities

Two kinds of glue that core Lean does not provide:

* A `decide`-friendly bridge for universally quantified facts about
  `UInt8` (used for the character-map lemmas, which `bv_decide` cannot
  handle because they involve `Char`). There is no `Decidable` instance
  for `∀ v : UInt8, P v`, so we reduce to a bounded quantifier over
  `Nat`, which `Nat.decidableBallLT` makes decidable.

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

theorem bext {a b : ByteArray} (h : a.data = b.data) : a = b := by
  cases a
  cases b
  simp only at h
  rw [h]

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

theorem toByteArray_push_ascii (s : String) (c : Char) (hc : c.utf8Size = 1) :
    (s.push c).toByteArray = s.toByteArray.push c.val.toUInt8 := by
  rw [String.toByteArray_push, List.utf8Encode_singleton,
    String.utf8EncodeChar_eq_singleton hc]
  generalize s.toByteArray = b
  cases b
  apply bext
  refine Array.toList_inj.mp ?_
  simp [-Array.toList_inj, ByteArray.push]

theorem emptyWithCapacity_eq (c : Nat) :
    ByteArray.emptyWithCapacity c = ByteArray.empty := by
  apply bext
  rfl

end Rfc4648
