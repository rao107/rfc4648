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

/-! ## Installing the fast path

`@[csimp]` swaps the compiled implementation of `encode`/`decode?` for
the fast versions; the substitution is justified by the equality proofs
above, so nothing is trusted beyond what the theorems already establish. -/

private def encodeImpl : ByteArray → String :=
  encodeFast alphabet

@[csimp]
private theorem encode_eq_encodeImpl : @encode = @encodeImpl :=
  funext fun data => (encodeFast_eq_model alphabet data).symm

private def decodeImpl : String → Option ByteArray :=
  decodeFast? alphabet

@[csimp]
private theorem decode?_eq_decodeImpl : @decode? = @decodeImpl :=
  funext fun s => (decodeFast?_eq_model alphabet s).symm

namespace Url

private def encodeImpl : ByteArray → String :=
  encodeFast Url.alphabet

@[csimp]
private theorem encode_eq_encodeImpl : @Url.encode = @Url.encodeImpl :=
  funext fun data => (encodeFast_eq_model Url.alphabet data).symm

private def decodeImpl : String → Option ByteArray :=
  decodeFast? Url.alphabet

@[csimp]
private theorem decode?_eq_decodeImpl : @Url.decode? = @Url.decodeImpl :=
  funext fun s => (decodeFast?_eq_model Url.alphabet s).symm

end Url

end Rfc4648.Base64
