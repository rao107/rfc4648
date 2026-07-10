# rfc4648

Formally verified implementations of the [RFC 4648](https://www.rfc-editor.org/rfc/rfc4648)
data encodings in Lean 4, with no dependencies beyond the Lean core library.

All five encodings defined by the RFC are implemented and proved correct:

| Namespace | Encoding | Alphabet |
|---|---|---|
| `Rfc4648.Base64` | Base 64 (§4) | `A–Z a–z 0–9 + /` |
| `Rfc4648.Base64.Url` | Base 64, URL-safe (§5) | `A–Z a–z 0–9 - _` |
| `Rfc4648.Base32` | Base 32 (§6) | `A–Z 2–7` |
| `Rfc4648.Base32.Hex` | Base 32, extended hex (§7) | `0–9 A–V` |
| `Rfc4648.Base16` | Base 16 (§8) | `0–9 A–F` |

## API

Each namespace exposes the same interface:

```lean
def encode  : ByteArray → String
def decode? : String → Option ByteArray
```

```lean
open Rfc4648

#eval Base64.encode "foobar".toUTF8            -- "Zm9vYmFy"
#eval Base32.encode "foo".toUTF8               -- "MZXW6==="
#eval Base64.decode? "aGk="                    -- some "hi" (as bytes)
#eval Base64.decode? "aGk"                     -- none (missing padding)
```

The core logic lives in `encodeList : List UInt8 → List Char` and
`decodeList : List Char → Option (List UInt8)`, defined by structural
recursion over encoding groups; `encode`/`decode?` are thin wrappers.

`decode?` is **strict** (RFC 4648 §3.5, §12): it accepts exactly the
canonical encodings. Inputs with non-alphabet characters (including
lowercase where the alphabet is uppercase), wrong length, misplaced or
missing padding, or non-zero pad bits are all rejected. In particular
`Base64.Url.decode?` requires padding even though §5 permits omitting it
in some protocols.

## Theorems

Every codec has the same verified specification (stated at both the list
level and the `ByteArray`/`String` level):

| Theorem | Statement |
|---|---|
| `decode?_encode` | `decode? (encode data) = some data` |
| `encode_decode?` | `decode? s = some data → encode data = s` |
| `length_encode` | exact output length, e.g. `4 * ((data.size + 2) / 3)` for base64 |
| `length_of_decode?` | accepted inputs have the canonical length |

Together, round-trip plus canonicity say `encode` and `decode?` form a
bijection between byte strings and canonical encodings. The RFC 4648 §10
test vectors (and a set of malformed-input rejections) are checked at
compile time with `#guard`.

All proofs use only Lean's standard axioms (`propext`,
`Classical.choice`, `Quot.sound`) — no `sorry`, no extra axioms, no
`native_decide`.

## Proof approach

- Finite bit-manipulation facts (e.g. reassembling a byte from its 6-bit
  pieces) are kernel-checked by `decide`. Since core Lean has no
  `Decidable` instance for `∀ v : UInt8, P v`, `Rfc4648/Util.lean`
  provides bridges through bounded `Nat` quantifiers
  (`Nat.decidableBallLT`), with bounds chosen to keep enumeration small
  (≤ 4096 cases).
- Character-map inverses (`ofChar?_eq_some`) are proved by case analysis
  over the alphabet ranges, since `Char` cannot be enumerated.
- The main theorems are structural inductions over encoding groups
  (3 bytes ↔ 4 chars for base64, 5 ↔ 8 for base32, 1 ↔ 2 for base16),
  with one branch per padding shape.
- The URL/hex variants reuse all bit-level lemmas from their parent
  codec; only the character maps and their lemmas differ.

## Building

```sh
lake build          # builds the library and runs all compile-time checks
lake exe rfc4648    # runs Main.lean
lake exe bench      # times encode/decode for all five alphabets (~40s)
```

## Benchmark

`Bench.lean` times `encode` and `decode?` for each alphabet over
random inputs from 16 B to 1 MiB, reporting per-call time and
throughput for the fastest of five trials. On one desktop core, encoding
runs at roughly 40–50 MiB/s for base32/base64 and 25–35 MiB/s for
base16; decoding is about a third slower. Throughput sags at the largest
sizes, where the intermediate `List Char`/`List UInt8` that each codec
builds costs more than the byte-shuffling itself.

Run it compiled, as above: `encodeList` and `decodeList` recurse once per
byte, and the interpreter (`lean --run`) overflows its stack well before
1 MiB.

Toolchain: `leanprover/lean4:v4.31.0` (see `lean-toolchain`). CI runs
`lake build` via [lean-action](https://github.com/leanprover/lean-action).
