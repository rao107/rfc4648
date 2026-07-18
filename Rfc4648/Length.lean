import Rfc4648.Base16
import Rfc4648.Base32
import Rfc4648.Base64

/-!
# Output-length theorems

Exact output lengths for the RFC 4648 codecs, at the list level
(generic in the alphabet) and lifted to `ByteArray`/`String` for each
concrete alphabet.

Base16 has no padding, so `n` bytes encode to exactly `2 * n`
characters. Base64 and base32 pad the final group, giving
`4 * ⌈n / 3⌉` and `8 * ⌈n / 5⌉` characters respectively — so valid
encodings always have length divisible by 4 (resp. 8). The decoder
directions are corollaries of canonicity: anything the strict decoder
accepts *is* an encoder output, so it has the encoder's length.
-/

namespace Rfc4648

/-! ## Base 16 (§8) -/

namespace Base16

/-- The encoding of `n` bytes has exactly `2 * n` characters. -/
theorem length_encodeList (α : Alphabet 16) : ∀ bs : List UInt8,
    (encodeList α bs).length = 2 * bs.length
  | [] => rfl
  | b :: rest => by
    simp only [encodeList, List.length_cons, length_encodeList α rest]
    omega

/-- Anything the strict decoder accepts is twice as long as its output. -/
theorem length_of_decodeList {α : Alphabet 16} {cs : List Char} {bs : List UInt8}
    (h : decodeList α cs = some bs) : cs.length = 2 * bs.length := by
  rw [← encodeList_decodeList α h, length_encodeList]

/-- Encoding length, lifted to `ByteArray`/`String`. -/
theorem length_encode (data : ByteArray) : (encode data).length = 2 * data.size := by
  rw [encode_eq_model, String.length_ofList, length_encodeList, ByteArray.length_toList]

/-- Decoding length, lifted to `ByteArray`/`String`. -/
theorem length_of_decode? {s : String} {data : ByteArray}
    (h : decode? s = some data) : s.length = 2 * data.size := by
  rw [← encode_decode? h, length_encode]

end Base16

/-! ## Base 32 (§6 / §7) -/

namespace Base32

/-- The encoding of `n` bytes has exactly `8 * ((n + 4) / 5)` characters. -/
theorem length_encodeList (α : Alphabet 32) : ∀ bs : List UInt8,
    (encodeList α bs).length = 8 * ((bs.length + 4) / 5)
  | [] => rfl
  | [_] => by simp [encodeList]
  | [_, _] => by simp [encodeList]
  | [_, _, _] => by simp [encodeList]
  | [_, _, _, _] => by simp [encodeList]
  | b0 :: b1 :: b2 :: b3 :: b4 :: rest => by
    simp only [encodeList, List.length_cons, length_encodeList α rest]
    omega

/-- Anything the strict decoder accepts has the padded encoding length of
its output. -/
theorem length_of_decodeList {α : Alphabet 32} {cs : List Char} {bs : List UInt8}
    (h : decodeList α cs = some bs) : cs.length = 8 * ((bs.length + 4) / 5) := by
  rw [← encodeList_decodeList α h, length_encodeList]

/-- Anything the strict decoder accepts has length divisible by 8. -/
theorem length_of_decodeList_mod {α : Alphabet 32} {cs : List Char} {bs : List UInt8}
    (h : decodeList α cs = some bs) : cs.length % 8 = 0 := by
  rw [length_of_decodeList h]
  omega

/-- Encoding length, lifted to `ByteArray`/`String`. -/
theorem length_encode (data : ByteArray) :
    (encode data).length = 8 * ((data.size + 4) / 5) := by
  rw [encode_eq_model, String.length_ofList, length_encodeList, ByteArray.length_toList]

/-- Decoding length, lifted to `ByteArray`/`String`. -/
theorem length_of_decode? {s : String} {data : ByteArray}
    (h : decode? s = some data) : s.length = 8 * ((data.size + 4) / 5) := by
  rw [← encode_decode? h, length_encode]

namespace Hex

/-- Encoding length, lifted to `ByteArray`/`String`. -/
theorem length_encode (data : ByteArray) :
    (encode data).length = 8 * ((data.size + 4) / 5) := by
  rw [encode_eq_model, String.length_ofList, length_encodeList, ByteArray.length_toList]

/-- Decoding length, lifted to `ByteArray`/`String`. -/
theorem length_of_decode? {s : String} {data : ByteArray}
    (h : decode? s = some data) : s.length = 8 * ((data.size + 4) / 5) := by
  rw [← encode_decode? h, length_encode]

end Hex

end Base32

/-! ## Base 64 (§4 / §5) -/

namespace Base64

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
  rw [encode_eq_model, String.length_ofList, length_encodeList, ByteArray.length_toList]

/-- Decoding length, lifted to `ByteArray`/`String`. -/
theorem length_of_decode? {s : String} {data : ByteArray}
    (h : decode? s = some data) : s.length = 4 * ((data.size + 2) / 3) := by
  rw [← encode_decode? h, length_encode]

namespace Url

/-- Encoding length, lifted to `ByteArray`/`String`. -/
theorem length_encode (data : ByteArray) :
    (encode data).length = 4 * ((data.size + 2) / 3) := by
  rw [encode_eq_model, String.length_ofList, length_encodeList, ByteArray.length_toList]

/-- Decoding length, lifted to `ByteArray`/`String`. -/
theorem length_of_decode? {s : String} {data : ByteArray}
    (h : decode? s = some data) : s.length = 4 * ((data.size + 2) / 3) := by
  rw [← encode_decode? h, length_encode]

end Url

end Base64

end Rfc4648
