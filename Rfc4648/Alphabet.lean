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

end Rfc4648
