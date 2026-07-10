/-!
# Shared proof utilities

Two kinds of glue that core Lean does not provide:

* `decide`-friendly bridges for universally quantified facts about `UInt8`.
  There is no `Decidable` instance for `∀ v : UInt8, P v`, so we reduce to a
  bounded quantifier over `Nat`, which `Nat.decidableBallLT` makes decidable.
  Bounded variants keep the enumeration small (e.g. 16·16 instead of 256²
  cases for facts about 4-bit values).

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

/-- Two-variable version of `uint8_all_lt`: `b₁ · b₂` cases, which keeps
`decide` fast when both bounds are small. -/
theorem uint8_all_lt₂ {b₁ b₂ : Nat} {P : UInt8 → UInt8 → Prop}
    (h : ∀ m : Nat, m < b₁ → ∀ n : Nat, n < b₂ →
      P (UInt8.ofNat m) (UInt8.ofNat n)) :
    ∀ x y : UInt8, x.toNat < b₁ → y.toNat < b₂ → P x y := fun x y hx hy => by
  have hp := h x.toNat hx y.toNat hy
  rwa [UInt8.ofNat_toNat, UInt8.ofNat_toNat] at hp

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

end Rfc4648
