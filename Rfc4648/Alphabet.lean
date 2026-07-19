import Rfc4648.Util

/-!
# RFC 4648 alphabets

An `Alphabet size` bundles the two character maps of an RFC 4648 base
encoding together with the three facts the codec proofs need about them.
The codecs (`Rfc4648.Base16`, `Rfc4648.Base32`, `Rfc4648.Base64`) are
parameterized over an alphabet of the appropriate size, so each variant
(§5 base64url, §7 base32hex) is a different `Alphabet` value applied to
the same verified codec.
-/

namespace Rfc4648

/-- The character maps of an RFC 4648 alphabet for values `0, …, size-1`,
with the properties the codec correctness proofs need:

* `ofChar?_toChar`: decoding inverts encoding on in-range values;
* `toChar_ne_pad`: no alphabet character collides with the pad `'='`;
* `ofChar?_eq_some`: any accepted character is in range and re-encodes
  to itself (this is what makes strict decoding canonical). -/
structure Alphabet (size : UInt8) where
  toChar : UInt8 → Char
  ofChar? : Char → Option UInt8
  ofChar?_toChar : ∀ v : UInt8, v < size → ofChar? (toChar v) = some v
  toChar_ne_pad : ∀ v : UInt8, v < size → toChar v ≠ '='
  ofChar?_eq_some : ∀ {c : Char} {v : UInt8},
    ofChar? c = some v → v < size ∧ toChar v = c

/-! ## The inverse table

The byte-level decoders look 6-bit (resp. 5-, 4-bit) values up by input
byte instead of calling `ofChar?` per character. `0xFF` marks bytes
outside the alphabet; it can never collide with an alphabet value, which
is below `size ≤ 128`. -/

/-- 256-entry inverse table: maps a byte to the value of the alphabet
character it encodes, or `0xFF` if it is not an alphabet byte. -/
def mkDTable {size : UInt8} (α : Alphabet size) : ByteArray :=
  (List.ofFn fun i : Fin 256 => (α.ofChar? (Char.ofNat i.val)).getD 0xFF).toByteArray

theorem mkDTable_get! {size : UInt8} (α : Alphabet size) (b : UInt8) :
    (mkDTable α).get! b.toNat = (α.ofChar? (Char.ofNat b.toNat)).getD 0xFF := by
  unfold mkDTable
  rw [get!_ofFn_toByteArray _ b.toNat_lt_size]

/-- Table lookup for an ASCII character's byte is `ofChar?` of the
character (with `0xFF` for `none`). -/
theorem mkDTable_ascii {size : UInt8} (α : Alphabet size) {c : Char}
    (hc : c.toNat < 128) :
    (mkDTable α).get! (c.val.toUInt8).toNat = (α.ofChar? c).getD 0xFF := by
  rw [mkDTable_get!, toNat_val_toUInt8 hc, Char.ofNat_toNat]

/-- For an ASCII-only alphabet, every byte `≥ 0x80` misses the table. -/
theorem mkDTable_high {size : UInt8} (α : Alphabet size)
    (hascii : ∀ {c : Char} {v : UInt8}, α.ofChar? c = some v → c.toNat < 128)
    {b : UInt8} (hb : 128 ≤ b.toNat) : (mkDTable α).get! b.toNat = 0xFF := by
  rw [mkDTable_get!]
  cases hv : α.ofChar? (Char.ofNat b.toNat) with
  | none => rfl
  | some v =>
    have hlt := hascii hv
    have h256 : b.toNat < 256 := b.toNat_lt_size
    rw [char_toNat_ofNat (by omega)] at hlt
    omega

/-! ## Step lemmas for byte-level decoders

Used by each codec's `decodeGoB_eq` to relate the character at the head
of the remaining input to the byte at the current position: an accepted
character is one byte that looks up to its value, `'='` is the byte
`61`, and a rejected character's first byte misses the table (its lead
byte is `≥ 0x80` if it is not ASCII). `hascii` — the alphabet accepts
only ASCII — is discharged per alphabet by its `ofChar?_ascii`. -/

/-- An alphabet value is below `size ≤ 255`, so it is never the sentinel
`0xFF`. -/
theorem ne_ff_of_some {size : UInt8} {α : Alphabet size} {c : Char} {v : UInt8}
    (hv : α.ofChar? c = some v) : v ≠ 0xFF := fun he => by
  have h := (α.ofChar?_eq_some hv).1
  subst he
  have h1 := UInt8.lt_iff_toNat_lt.mp h
  have h2 : size.toNat < 256 := size.toNat_lt_size
  have h3 : (0xFF : UInt8).toNat = 255 := rfl
  omega

/-- An accepted character: its byte looks up to its value, is not `'='`,
and the input advances one byte. -/
theorem step_some {size : UInt8} {α : Alphabet size}
    (hascii : ∀ {c : Char} {v : UInt8}, α.ofChar? c = some v → c.toNat < 128)
    {c : Char} {v : UInt8} (hv : α.ofChar? c = some v)
    {l : List Char} {bs : ByteArray} {j : Nat}
    (hbs : bs.toList.drop j = ((c :: l).utf8Encode).toList) :
    ∃ h : j < bs.size,
      (mkDTable α).get! (bs[j]'h).toNat = v ∧ bs[j]'h ≠ 61 ∧
      bs.toList.drop (j + 1) = (l.utf8Encode).toList := by
  have hc := hascii hv
  obtain ⟨h, hb, hrest⟩ := drop_utf8_ascii hc hbs
  refine ⟨h, ?_, ?_, hrest⟩
  · rw [hb, mkDTable_ascii α hc, hv]
    rfl
  · rw [hb]
    intro heq
    have hpad : c = '=' := ascii_byte_inj hc (by decide) heq
    subst hpad
    obtain ⟨hlt, htc⟩ := α.ofChar?_eq_some hv
    exact α.toChar_ne_pad v hlt htc

/-- The padding character: its byte is `61`, and the input advances one
byte. -/
theorem step_pad {l : List Char} {bs : ByteArray} {j : Nat}
    (hbs : bs.toList.drop j = (('=' :: l).utf8Encode).toList) :
    ∃ h : j < bs.size, bs[j]'h = 61 ∧
      bs.toList.drop (j + 1) = (l.utf8Encode).toList := by
  obtain ⟨h, hb, hrest⟩ := drop_utf8_ascii (by decide) hbs
  exact ⟨h, hb, hrest⟩

/-- A character other than `'='` never starts with the byte `61`:
an ASCII character is its own (distinct) byte, and a non-ASCII
character starts with a lead byte `≥ 0x80`. -/
theorem step_not_pad {c : Char} (hpad : c ≠ '=') {l : List Char}
    {bs : ByteArray} {j : Nat}
    (hbs : bs.toList.drop j = ((c :: l).utf8Encode).toList) :
    ∃ h : j < bs.size, bs[j]'h ≠ 61 := by
  by_cases hc : c.toNat < 128
  · obtain ⟨h, hb, -⟩ := drop_utf8_ascii hc hbs
    refine ⟨h, fun heq => ?_⟩
    rw [hb] at heq
    exact hpad (ascii_byte_inj hc (by decide) heq)
  · obtain ⟨h, hhigh⟩ := drop_utf8_high (Nat.le_of_not_lt hc) hbs
    refine ⟨h, fun heq => ?_⟩
    rw [heq] at hhigh
    exact absurd hhigh (by decide)

/-- A rejected character: its first byte misses the table. -/
theorem step_none {size : UInt8} {α : Alphabet size}
    (hascii : ∀ {c : Char} {v : UInt8}, α.ofChar? c = some v → c.toNat < 128)
    {c : Char} (hv : α.ofChar? c = none) {l : List Char}
    {bs : ByteArray} {j : Nat}
    (hbs : bs.toList.drop j = ((c :: l).utf8Encode).toList) :
    ∃ h : j < bs.size, (mkDTable α).get! (bs[j]'h).toNat = 0xFF := by
  by_cases hc : c.toNat < 128
  · obtain ⟨h, hb, -⟩ := drop_utf8_ascii hc hbs
    exact ⟨h, by rw [hb, mkDTable_ascii α hc, hv]; rfl⟩
  · obtain ⟨h, hhigh⟩ := drop_utf8_high (Nat.le_of_not_lt hc) hbs
    exact ⟨h, mkDTable_high α hascii hhigh⟩

/-- A rejected character that is not `'='`: its first byte misses the
table and is not `61` either. -/
theorem step_bad {size : UInt8} {α : Alphabet size}
    (hascii : ∀ {c : Char} {v : UInt8}, α.ofChar? c = some v → c.toNat < 128)
    {c : Char} (hv : α.ofChar? c = none) (hpad : c ≠ '=')
    {l : List Char} {bs : ByteArray} {j : Nat}
    (hbs : bs.toList.drop j = ((c :: l).utf8Encode).toList) :
    ∃ h : j < bs.size,
      (mkDTable α).get! (bs[j]'h).toNat = 0xFF ∧ bs[j]'h ≠ 61 := by
  by_cases hc : c.toNat < 128
  · obtain ⟨h, hb, -⟩ := drop_utf8_ascii hc hbs
    refine ⟨h, by rw [hb, mkDTable_ascii α hc, hv]; rfl, ?_⟩
    rw [hb]
    exact fun heq => hpad (ascii_byte_inj hc (by decide) heq)
  · obtain ⟨h, hhigh⟩ := drop_utf8_high (Nat.le_of_not_lt hc) hbs
    refine ⟨h, mkDTable_high α hascii hhigh, ?_⟩
    intro heq
    rw [heq] at hhigh
    exact absurd hhigh (by decide)

end Rfc4648
