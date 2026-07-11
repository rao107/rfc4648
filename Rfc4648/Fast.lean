import Std.Tactic.BVDecide
import Rfc4648.Base64

/-!
# Verified fast path for base64

`Base64.encode`/`decode?` (and their `Url` counterparts) are defined via
the list-model codec, which allocates a cons cell per character. This
module provides allocation-free implementations — the encoder indexes
straight into the `ByteArray` and pushes onto a `String`, the decoder
pushes onto a `ByteArray` accumulator — proves them equal to the model,
and installs them with `@[csimp]`: compiled code (the CLI, the benchmark,
downstream users) runs the fast versions, while every theorem about
`encode`/`decode?` continues to hold, justified by the machine-checked
equality rather than trust.
-/

namespace Rfc4648.Base64

/-! ## Implementations -/

/-- Tail-recursive base64 encoder: reads 3-byte groups directly from
`data` starting at `i`, pushing characters onto `acc`. -/
private def encodeGo (α : Alphabet 64) (data : ByteArray) (i : Nat) (acc : String) : String :=
  if h3 : i + 3 ≤ data.size then
    encodeGo α data (i + 3) <| (((acc.push
      (α.toChar (data[i]'(by omega) >>> 2))).push
      (α.toChar (((data[i]'(by omega) &&& 0x03) <<< 4) ||| (data[i + 1]'(by omega) >>> 4)))).push
      (α.toChar (((data[i + 1]'(by omega) &&& 0x0F) <<< 2) ||| (data[i + 2]'(by omega) >>> 6)))).push
      (α.toChar (data[i + 2]'(by omega) &&& 0x3F))
  else if h1 : data.size = i + 1 then
    (((acc.push
      (α.toChar (data[i]'(by omega) >>> 2))).push
      (α.toChar ((data[i]'(by omega) &&& 0x03) <<< 4))).push '=').push '='
  else if h2 : data.size = i + 2 then
    (((acc.push
      (α.toChar (data[i]'(by omega) >>> 2))).push
      (α.toChar (((data[i]'(by omega) &&& 0x03) <<< 4) ||| (data[i + 1]'(by omega) >>> 4)))).push
      (α.toChar ((data[i + 1]'(by omega) &&& 0x0F) <<< 2))).push '='
  else acc
termination_by data.size - i

/-- Base64 encoder without intermediate lists. Equal to
`String.ofList (encodeList α data.toList)` by `encodeFast_eq_model`. -/
def encodeFast (α : Alphabet 64) (data : ByteArray) : String :=
  encodeGo α data 0 ""

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

/-- Base64 decoder that accumulates into a `ByteArray` instead of
building a `List UInt8`. Equal to `decode?`'s body by
`decodeFast?_eq_model`. -/
def decodeFast? (α : Alphabet 64) (s : String) : Option ByteArray :=
  decodeGo α s.toList ByteArray.empty

/-! ## Equivalence with the list model -/

section Model

private theorem str_ext {a b : String} (h : a.toList = b.toList) : a = b := by
  have hab := congrArg String.ofList h
  rwa [String.ofList_toList, String.ofList_toList] at hab

private theorem bext {a b : ByteArray} (h : a.data = b.data) : a = b := by
  cases a
  cases b
  simp only at h
  rw [h]

private theorem toList_getElem (data : ByteArray) (j : Nat) (h : j < data.size) :
    data.toList[j]'(by rw [ByteArray.length_toList]; exact h) = data[j] := by
  cases data with
  | mk arr => simp [ByteArray.toList_eq_data_toList]; rfl

private theorem drop_cons (data : ByteArray) (i : Nat) (h : i < data.size) :
    data.toList.drop i = data[i] :: data.toList.drop (i + 1) := by
  rw [List.drop_eq_getElem_cons (by rw [ByteArray.length_toList]; exact h),
    toList_getElem data i h]

private theorem drop_of_size_le (data : ByteArray) (i : Nat) (h : data.size ≤ i) :
    data.toList.drop i = [] :=
  List.drop_eq_nil_of_le (by rw [ByteArray.length_toList]; exact h)

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

private theorem encodeGo_eq (α : Alphabet 64) (data : ByteArray) (i : Nat) (acc : String) :
    encodeGo α data i acc = acc ++ String.ofList (encodeList α (data.toList.drop i)) := by
  fun_induction encodeGo α data i acc with
  | case1 i acc h3 ih =>
    rw [ih, drop_three data i (by omega)]
    apply str_ext
    simp [String.toList_append, String.toList_push, encodeList]
  | case2 i acc h3 h1 =>
    rw [drop_cons data i (by omega), drop_of_size_le data (i + 1) (by omega)]
    apply str_ext
    simp [String.toList_append, String.toList_push, encodeList]
  | case3 i acc h3 h1 h2 =>
    rw [drop_two data i (by omega), drop_of_size_le data (i + 2) (by omega)]
    apply str_ext
    simp [String.toList_append, String.toList_push, encodeList]
  | case4 i acc h3 h1 h2 =>
    rw [drop_of_size_le data i (by omega)]
    apply str_ext
    simp [encodeList]

/-- The fast encoder computes exactly the model encoding. -/
theorem encodeFast_eq_model (α : Alphabet 64) (data : ByteArray) :
    encodeFast α data = String.ofList (encodeList α data.toList) := by
  rw [encodeFast, encodeGo_eq]
  apply str_ext
  simp

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

/-- The fast decoder computes exactly the model decoding. -/
theorem decodeFast?_eq_model (α : Alphabet 64) (s : String) :
    decodeFast? α s = (decodeList α s.toList).map fun l => ByteArray.mk l.toArray := by
  rw [decodeFast?, decodeGo_eq]
  cases decodeList α s.toList with
  | none => rfl
  | some l =>
    simp only [Option.map_some]
    exact congrArg some (bext (by
      rw [show ByteArray.empty.data = #[] from rfl]
      simp))

end Model

/-! ## Byte-level encoder

`encodeFast` still pays per character for `α.toChar` (a comparison chain
plus a `Char.ofNat` validity check) and for `String.push` (UTF-8 size
dispatch). This encoder precomputes the alphabet's 64 UTF-8 bytes in a
table and pushes raw bytes onto a `ByteArray`, then wraps the result as
a `String` via the *unchecked* runtime constructor — the `IsValidUTF8`
obligation is discharged by the equality proof with `encodeGo`, whose
output is a `String` and therefore valid. The proof does the work the
runtime would otherwise do. -/

/-- The alphabet's characters as their single UTF-8 bytes. -/
private def mkTable (α : Alphabet 64) : ByteArray :=
  (List.ofFn fun i : Fin 64 => (α.toChar (UInt8.ofNat i.val)).val.toUInt8).toByteArray

/-- Byte-level base64 encoder over a precomputed alphabet table. -/
private def encodeGoB (tbl : ByteArray) (data : ByteArray) (i : Nat) (acc : ByteArray) :
    ByteArray :=
  if h3 : i + 3 ≤ data.size then
    encodeGoB tbl data (i + 3) <| (((acc.push
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

section ByteModel

private theorem v0_lt (b0 : UInt8) : b0 >>> 2 < 64 := by bv_decide

private theorem v1_lt (b0 b1 : UInt8) :
    ((b0 &&& 0x03) <<< 4) ||| (b1 >>> 4) < 64 := by bv_decide

private theorem v1p_lt (b0 : UInt8) : (b0 &&& 0x03) <<< 4 < 64 := by bv_decide

private theorem v2_lt (b1 b2 : UInt8) :
    ((b1 &&& 0x0F) <<< 2) ||| (b2 >>> 6) < 64 := by bv_decide

private theorem v2p_lt (b1 : UInt8) : (b1 &&& 0x0F) <<< 2 < 64 := by bv_decide

private theorem v3_lt (b2 : UInt8) : b2 &&& 0x3F < 64 := by bv_decide

private theorem get!_eq (b : ByteArray) (i : Nat) : b.get! i = b.data[i]! := by
  cases b
  rfl

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

private theorem toByteArray_push_ascii (s : String) (c : Char) (hc : c.utf8Size = 1) :
    (s.push c).toByteArray = s.toByteArray.push c.val.toUInt8 := by
  rw [String.toByteArray_push, List.utf8Encode_singleton,
    String.utf8EncodeChar_eq_singleton hc]
  generalize s.toByteArray = b
  cases b
  apply bext
  refine Array.toList_inj.mp ?_
  simp [-Array.toList_inj, ByteArray.push]

private theorem encodeGoB_eq (α : Alphabet 64)
    (h : ∀ v : UInt8, v < 64 → (α.toChar v).utf8Size = 1) (data : ByteArray)
    (i : Nat) (acc : ByteArray) (sacc : String) (hacc : acc = sacc.toByteArray) :
    encodeGoB (mkTable α) data i acc = (encodeGo α data i sacc).toByteArray := by
  revert sacc hacc
  fun_induction encodeGoB (mkTable α) data i acc with
  | case1 i acc h3 ih =>
    intro sacc hacc
    rw [encodeGo.eq_def, dif_pos h3]
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
    rw [encodeGo.eq_def, dif_neg h3, dif_pos h1]
    subst hacc
    rw [toByteArray_push_ascii _ _ (by decide : ('=' : Char).utf8Size = 1),
      toByteArray_push_ascii _ _ (by decide : ('=' : Char).utf8Size = 1),
      toByteArray_push_ascii _ _ (h _ (v1p_lt _)),
      toByteArray_push_ascii _ _ (h _ (v0_lt _)),
      mkTable_get! α (v0_lt _), mkTable_get! α (v1p_lt _)]
  | case3 i acc h3 h1 h2 =>
    intro sacc hacc
    rw [encodeGo.eq_def, dif_neg h3, dif_neg h1, dif_pos h2]
    subst hacc
    rw [toByteArray_push_ascii _ _ (by decide : ('=' : Char).utf8Size = 1),
      toByteArray_push_ascii _ _ (h _ (v2p_lt _)),
      toByteArray_push_ascii _ _ (h _ (v1_lt _ _)),
      toByteArray_push_ascii _ _ (h _ (v0_lt _)),
      mkTable_get! α (v0_lt _), mkTable_get! α (v1_lt _ _),
      mkTable_get! α (v2p_lt _)]
  | case4 i acc h3 h1 h2 =>
    intro sacc hacc
    rw [encodeGo.eq_def, dif_neg h3, dif_neg h1, dif_neg h2]
    exact hacc

end ByteModel

private theorem emptyWithCapacity_eq (c : Nat) :
    ByteArray.emptyWithCapacity c = ByteArray.empty := by
  apply bext
  rfl

/-- Byte-level base64 encoder. The alphabet table is passed in (so
callers can hoist it to a constant computed once), the output buffer is
preallocated at the exact final size, and the `IsValidUTF8` obligation
of the unchecked `String` constructor is discharged via the equality
with the `String`-level encoder — no validation happens at runtime. -/
def encodeFaster (α : Alphabet 64)
    (h : ∀ v : UInt8, v < 64 → (α.toChar v).utf8Size = 1)
    (tbl : ByteArray) (htbl : tbl = mkTable α) (data : ByteArray) : String :=
  String.ofByteArray
    (encodeGoB tbl data 0 (ByteArray.emptyWithCapacity (4 * ((data.size + 2) / 3))))
    (by
      rw [htbl, emptyWithCapacity_eq,
        encodeGoB_eq α h data 0 ByteArray.empty "" rfl]
      exact (encodeGo α data 0 "").isValidUTF8)

/-- The byte-level encoder computes exactly the model encoding. -/
theorem encodeFaster_eq_model (α : Alphabet 64)
    (h : ∀ v : UInt8, v < 64 → (α.toChar v).utf8Size = 1)
    (tbl : ByteArray) (htbl : tbl = mkTable α) (data : ByteArray) :
    encodeFaster α h tbl htbl data = String.ofList (encodeList α data.toList) := by
  rw [← encodeFast_eq_model, ← String.toByteArray_inj]
  show encodeGoB tbl data 0 _ = _
  rw [htbl, emptyWithCapacity_eq]
  exact encodeGoB_eq α h data 0 ByteArray.empty "" rfl

/-! ## Installing the fast path

`@[csimp]` swaps the compiled implementation of `encode`/`decode?` for
the fast versions; the substitution is justified by the equality proofs
above, so nothing is trusted beyond what the theorems already establish. -/

section Ascii

set_option maxRecDepth 4096

private theorem alphabet_ascii : ∀ v : UInt8, v < 64 →
    (alphabet.toChar v).utf8Size = 1 :=
  uint8_all (by decide)

private theorem url_alphabet_ascii : ∀ v : UInt8, v < 64 →
    (Url.alphabet.toChar v).utf8Size = 1 :=
  uint8_all (by decide)

end Ascii

/-- The §4 alphabet table, computed once at initialization. -/
private def stdTable : ByteArray := mkTable alphabet

private def encodeImpl : ByteArray → String :=
  encodeFaster alphabet alphabet_ascii stdTable rfl

@[csimp]
private theorem encode_eq_encodeImpl : @encode = @encodeImpl :=
  funext fun data =>
    (encodeFaster_eq_model alphabet alphabet_ascii stdTable rfl data).symm

private def decodeImpl : String → Option ByteArray :=
  decodeFast? alphabet

@[csimp]
private theorem decode?_eq_decodeImpl : @decode? = @decodeImpl :=
  funext fun s => (decodeFast?_eq_model alphabet s).symm

namespace Url

/-- The §5 alphabet table, computed once at initialization. -/
private def urlTable : ByteArray := mkTable Url.alphabet

private def encodeImpl : ByteArray → String :=
  encodeFaster Url.alphabet url_alphabet_ascii urlTable rfl

@[csimp]
private theorem encode_eq_encodeImpl : @Url.encode = @Url.encodeImpl :=
  funext fun data =>
    (encodeFaster_eq_model Url.alphabet url_alphabet_ascii urlTable rfl data).symm

private def decodeImpl : String → Option ByteArray :=
  decodeFast? Url.alphabet

@[csimp]
private theorem decode?_eq_decodeImpl : @Url.decode? = @Url.decodeImpl :=
  funext fun s => (decodeFast?_eq_model Url.alphabet s).symm

end Url

end Rfc4648.Base64
