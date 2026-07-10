import Rfc4648

/-!
# Throughput benchmark

Times `encode` and `decode?` for each of the five RFC 4648 alphabets over random
inputs of increasing length.
-/

structure Codec where
  name : String
  encode : ByteArray → String
  decode? : String → Option ByteArray

def codecs : List Codec :=
  [ { name := "base16",    encode := Rfc4648.Base16.encode,     decode? := Rfc4648.Base16.decode? }
  , { name := "base32",    encode := Rfc4648.Base32.encode,     decode? := Rfc4648.Base32.decode? }
  , { name := "base32hex", encode := Rfc4648.Base32.Hex.encode, decode? := Rfc4648.Base32.Hex.decode? }
  , { name := "base64",    encode := Rfc4648.Base64.encode,     decode? := Rfc4648.Base64.decode? }
  , { name := "base64url", encode := Rfc4648.Base64.Url.encode, decode? := Rfc4648.Base64.Url.decode? } ]

/-! ## Measurement

Input is drawn fresh each run, not from a seed: these codecs have no
data-dependent control flow, so the timings do not depend on the bytes.
-/

/-- Bytes per trial; sets the iteration count so every size does equal work. -/
def workPerCell : Nat := 1 <<< 21

def iterationsFor (size : Nat) : Nat := max 3 (workPerCell / size)

/-- Trials per measurement; we keep the fastest, since noise only adds time.
The 256 KiB and 1 MiB rows still swing ~20% on allocator and GC pressure. -/
def trials : Nat := 5

/-- Elapsed nanoseconds for `iters` calls, plus a checksum of the results.

`arg` is passed in, not captured: a closure body mentioning none of its
parameters is a closed term that the compiler evaluates once, so every
iteration would return a cached value. The checksum likewise keeps the calls
from being dropped as dead code. -/
def timed (iters : Nat) (arg : α) (act : α → Nat) : IO (Nat × Nat) := do
  let mut checksum := 0
  let t0 ← IO.monoNanosNow
  for _ in [0:iters] do
    checksum := checksum ^^^ act arg
  let t1 ← IO.monoNanosNow
  return (t1 - t0, checksum)

/-- Nanoseconds for the fastest of `trials` runs. -/
def bestOf (iters : Nat) (arg : α) (act : α → Nat) : IO Nat := do
  let mut best := none
  for _ in [0:trials] do
    let (nanos, _) ← timed iters arg act
    best := some (min (best.getD nanos) nanos)
  return best.getD 0

/-! ## Reporting -/

def padLeft (width : Nat) (s : String) : String :=
  "".pushn ' ' (width - s.length) ++ s

def padRight (width : Nat) (s : String) : String :=
  s.pushn ' ' (width - s.length)

/-- Format to two decimal places. -/
def fmt2 (x : Float) : String :=
  let scaled := (x * 100.0).round.toUInt64.toNat
  let whole := scaled / 100
  let frac := scaled % 100
  s!"{whole}.{padLeft 2 (toString frac) |>.replace " " "0"}"

/-- Human-readable byte count, e.g. `4.00 KiB`. -/
def fmtSize (n : Nat) : String :=
  if n < 1024 then s!"{n} B"
  else if n < 1 <<< 20 then s!"{fmt2 (n.toFloat / 1024.0)} KiB"
  else s!"{fmt2 (n.toFloat / 1048576.0)} MiB"

/-- `iters` passes over `size` bytes in `nanos`, as MiB/s. -/
def throughput (size iters nanos : Nat) : Float :=
  if nanos == 0 then 0.0
  else (size * iters).toFloat / 1048576.0 / (nanos.toFloat / 1e9)

/-- One row: size, iterations, per-call time and throughput, both directions. -/
def benchOne (c : Codec) (size : Nat) : IO Unit := do
  let input ← IO.getRandomBytes size.toUSize
  let encoded := c.encode input
  -- A rejected input decodes to `none` at once, which would read as excellent
  -- throughput. The input is random, so print it on failure.
  unless c.decode? encoded == some input do
    throw <| IO.userError s!"{c.name}: round trip failed at {size} bytes\n\
      input:   {input.toList.map (·.toNat)}\n\
      encoded: {encoded}"
  -- `utf8ByteSize` is cached; `String.length` would count codepoints on the clock.
  let encodeOnce := fun (d : ByteArray) => (c.encode d).utf8ByteSize
  let decodeOnce := fun (s : String) => ((c.decode? s).map ByteArray.size).getD 0
  -- Warm up: fault in pages and settle the allocator.
  let _ ← timed 1 input encodeOnce
  let _ ← timed 1 encoded decodeOnce
  let iters := iterationsFor size
  let encNanos ← bestOf iters input encodeOnce
  let decNanos ← bestOf iters encoded decodeOnce
  let perCall (nanos : Nat) : String :=
    let us := nanos.toFloat / iters.toFloat / 1000.0
    s!"{fmt2 us} us"
  IO.println <| String.intercalate "  "
    [ padLeft 10 (fmtSize size)
    , padLeft 6 (toString iters)
    , padLeft 13 (perCall encNanos)
    , padLeft 11 (fmt2 (throughput size iters encNanos))
    , padLeft 13 (perCall decNanos)
    , padLeft 11 (fmt2 (throughput size iters decNanos)) ]

/-- `encodeList`/`decodeList` recurse once per byte, so much past 1 MiB
overflows the stack. Run compiled (`lake exe bench`); `lean --run` has a
smaller stack and overflows well before that. -/
def sizes : List Nat := [16, 64, 256, 1024, 4096, 16384, 65536, 262144, 1048576]

def header : String := String.intercalate "  "
  [ padLeft 10 "input", padLeft 6 "iters"
  , padLeft 13 "encode", padLeft 11 "MiB/s"
  , padLeft 13 "decode", padLeft 11 "MiB/s" ]

def main : IO Unit := do
  IO.println s!"RFC 4648 throughput (best of {trials} trials, \
    {workPerCell / 1048576} MiB per trial)\n"
  for c in codecs do
    IO.println (padRight 10 c.name)
    IO.println header
    IO.println ("".pushn '-' header.length)
    for size in sizes do
      benchOne c size
    IO.println ""
