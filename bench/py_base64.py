#!/usr/bin/env python3
"""base64 throughput via the CPython stdlib `base64` module (C-backed).

Mirrors LeanBase64.lean: same sizes, best-of-5 trials, one warmup. Emits CSV
`python,<size>,<encode MiB/s>,<decode MiB/s>` on stdout."""
import base64, os, time

SIZES = [16, 64, 256, 1024, 4096, 16384, 65536, 262144, 1048576]
WORK = 1 << 21
TRIALS = 5


def best(iters, fn, arg):
    b = None
    for _ in range(TRIALS):
        t0 = time.perf_counter_ns()
        cs = 0
        for _ in range(iters):
            cs ^= fn(arg)
        d = time.perf_counter_ns() - t0
        if b is None or d < b:
            b = d
    return b


def mibps(size, iters, nanos):
    return size * iters / (1 << 20) / (nanos / 1e9)


enc = lambda d: len(base64.b64encode(d))
dec = lambda s: len(base64.b64decode(s))

for size in SIZES:
    data = os.urandom(size)
    encoded = base64.b64encode(data)
    iters = max(3, WORK // size)
    best(1, enc, data)
    best(1, dec, encoded)
    en = best(iters, enc, data)
    dn = best(iters, dec, encoded)
    print(f"python,{size},{mibps(size, iters, en):.2f},{mibps(size, iters, dn):.2f}")
