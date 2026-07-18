import Rfc4648

/-!
# base64 throughput for the verified codec, CSV output

Measures this project's `Base64.encode` / `decode?` — defined directly as
the verified byte-level fast path — with the same methodology as
the other `bench/` programs (same sizes, best of five trials, one warmup) and
emits CSV `lean,<size>,<encode MiB/s>,<decode MiB/s>` on stdout. Driven by
`bench/run.sh`.

Build compiled (`lake exe bench`); the interpreter has a smaller stack.
-/

def sizes : List Nat := [16, 64, 256, 1024, 4096, 16384, 65536, 262144, 1048576]
def workPerCell : Nat := 1 <<< 21
def trials : Nat := 5
def iterationsFor (size : Nat) : Nat := max 3 (workPerCell / size)

/-- Elapsed nanoseconds for `iters` calls, plus a checksum of the results.
The checksum is returned (not just accumulated) so the calls are not dropped
as dead code, and `arg` is passed in rather than captured so the closure is
not a cached closed term. -/
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

/-- `iters` passes over `size` bytes in `nanos`, as MiB/s. -/
def throughput (size iters nanos : Nat) : Float :=
  if nanos == 0 then 0.0
  else (size * iters).toFloat / 1048576.0 / (nanos.toFloat / 1e9)

def main : IO Unit := do
  for size in sizes do
    let input ← IO.getRandomBytes size.toUSize
    let encoded := Rfc4648.Base64.encode input
    -- A rejected input would decode to `none` at once and read as huge
    -- throughput; the input is random, so guard the round trip.
    unless Rfc4648.Base64.decode? encoded == some input do
      throw <| IO.userError s!"lean: round trip failed at {size} bytes"
    let encodeOnce := fun (d : ByteArray) => (Rfc4648.Base64.encode d).utf8ByteSize
    let decodeOnce := fun (s : String) => ((Rfc4648.Base64.decode? s).map ByteArray.size).getD 0
    let _ ← timed 1 input encodeOnce
    let _ ← timed 1 encoded decodeOnce
    let iters := iterationsFor size
    let encNanos ← bestOf iters input encodeOnce
    let decNanos ← bestOf iters encoded decodeOnce
    IO.println s!"lean,{size},{throughput size iters encNanos},{throughput size iters decNanos}"
