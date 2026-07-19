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

The specification lives in `encodeList : List UInt8 → List Char` and
`decodeList : List Char → Option (List UInt8)`, defined by structural
recursion over encoding groups; `encode`/`decode?` are efficient
implementations proved equal to it (see each codec's
`encode_eq_model`/`decode?_eq_model`), so every theorem about the
specification carries over to them. All encoders and decoders are
byte-level and table-driven.

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

There are no `sorry`s. Besides Lean's standard axioms (`propext`,
`Classical.choice`, `Quot.sound`), proofs that use `bv_decide` depend on
per-theorem `…._native.bv_decide.ax_*` axioms: the SAT solver's
unsatisfiability certificate is checked by a verified checker that runs
as compiled native code, so these proofs trust the Lean compiler in
addition to the kernel. The character-map lemmas avoid this and are
kernel-checked by plain `decide`.

## Proof approach

- The codecs are parameterized over an `Alphabet size` structure
  (`Rfc4648/Alphabet.lean`) bundling the character maps with the three
  facts the proofs need. Round-trip, canonicity, and length are proved
  once per bit-width family; §5 base64url and §7 base32hex are just
  different `Alphabet` values applied to the same theorems.
- Bit-manipulation facts (e.g. reassembling a byte from its 6-bit
  pieces) are discharged by `bv_decide`, stated directly over full
  `UInt8`s with `<` hypotheses where needed — no case enumeration.
- Character-map lemmas are discharged by `decide` via bounded-`Nat`
  bridges in `Rfc4648/Util.lean` (`Nat.decidableBallLT`): the forward
  direction (`ofChar?_toChar`) enumerates the 256 byte values, and the
  inverse direction (`ofChar?_eq_some`) — where `Char` itself cannot be
  enumerated — first bounds accepted characters to ASCII and then
  enumerates the 128 code points.
- The main theorems are structural inductions over encoding groups
  (3 bytes ↔ 4 chars for base64, 5 ↔ 8 for base32, 1 ↔ 2 for base16),
  with one branch per padding shape.
- The byte-level decoders are proved equal to the character-level
  specification with a little verified UTF-8 reasoning
  (`Rfc4648/Util.lean`): an ASCII character is exactly its code point as
  one byte, a non-ASCII character starts with a lead byte `≥ 0x80`, and
  the 256-entry inverse table rejects every such byte — so accepted
  bytes are in one-to-one correspondence with accepted characters, and
  the decoder never has to decode UTF-8.

## Building

```sh
lake build          # builds the library and runs all compile-time checks
lake exe rfc4648    # runs Main.lean
bench/run.sh        # base64 throughput vs. mainstream languages (see Benchmark)
```

## Benchmark

`bench/run.sh` compares this project's base64 against mainstream
implementations in other languages over the same workload — random inputs
from 16 B to 1 MiB, per direction, best of five trials with one warmup:

- **Lean (this project)** — the verified `Base64.encode` / `decode?`,
  defined directly as the byte-level fast path
  (`bench/LeanBase64.lean`, run compiled via `lake exe bench`);
- **Python** `base64` (stdlib, C-backed), **Node** `Buffer` (native),
  **Go** `encoding/base64` (stdlib), **C** via OpenSSL `libcrypto`
  (`EVP_EncodeBlock`/`EVP_DecodeBlock`), and the **Rust** `base64` crate
  (0.22).

Each program mirrors the same methodology and emits CSV;
`bench/run.sh` builds and runs them all and `bench/compare.py` prints the
table:

```sh
bench/run.sh            # full comparison (~1–2 min; builds the Rust crate first time)
bench/run.sh --no-lean  # skip the Lean build/run
```

`Base64.encode` is a byte-level encoder that reads 3-byte groups
straight from the input, looks characters up in a precomputed table,
pushes raw bytes into an exactly-sized buffer, and wraps the result with
the *unchecked* `String` constructor — its `IsValidUTF8` obligation is
discharged by the proof that the output equals the list model's, so the
validation the runtime would do is replaced by a theorem, and every
theorem stated against the specification transfers through the
machine-checked equality `encode_eq_model`.

`Base64.decode?` got the mirror-image treatment: it reads the string's
UTF-8 bytes directly through a 256-entry inverse table that rejects
every non-alphabet byte. It never decodes UTF-8 — the proof
`decodeGoB_eq` shows accepted bytes are in one-to-one correspondence
with the characters of the specification, which is what transfers the
round-trip and canonicity theorems. This replaced a `List Char` walk
that managed only ~25 MiB/s, a ~13× speedup.

Representative single-core throughput at 1 MiB (MiB/s; higher is better;
numbers swing noticeably run to run with CPU frequency scaling, so treat
the ratios as indicative):

| implementation | encode | decode |
|---|--:|--:|
| **Lean (this project)** | ~330 | ~340 |
| C — OpenSSL `libcrypto` | ~2600 | ~2270 |
| Rust — `base64` 0.22 | ~2760 | ~1950 |
| Go — `encoding/base64` | ~1110 | ~1540 |
| Node — `Buffer` | ~2600 | ~3300 |
| Python — `base64` | ~960 | ~1160 |

Both directions of the verified codec now land in the same order of
magnitude as the scalar/stdlib field — within ~3–5× of Go and Python's
C core — while OpenSSL and the SIMD-accelerated Rust crate run ~6–8×
faster still. The remaining gap is per-byte `ByteArray.push` and
`get!` bounds checks versus the word-at-a-time loops the C-family
implementations use.

Toolchain: `leanprover/lean4:v4.31.0` (see `lean-toolchain`). CI runs
`lake build` via [lean-action](https://github.com/leanprover/lean-action).
