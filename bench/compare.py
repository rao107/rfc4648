#!/usr/bin/env python3
"""Aggregate the per-language CSVs (and the Lean bench output) in a directory
into two comparison tables: encode MiB/s and decode MiB/s, one row per size.

Usage: compare.py <dir>
  <dir> holds `<impl>.csv` files (impl,size,encode_mibps,decode_mibps)."""
import glob, os, sys

SIZES = [16, 64, 256, 1024, 4096, 16384, 65536, 262144, 1048576]

# Display name and column order for the implementations we know about.
LABELS = {
    "lean": "Lean (verified)",
    "c": "C (OpenSSL)",
    "rust": "Rust (base64)",
    "go": "Go (stdlib)",
    "node": "Node (Buffer)",
    "python": "Python (stdlib)",
}
ORDER = ["lean", "c", "rust", "go", "node", "python"]


def human(n):
    if n < 1024:
        return f"{n} B"
    if n < 1 << 20:
        return f"{n // 1024} KiB"
    return f"{n // (1 << 20)} MiB"


def load(outdir):
    data = {}  # impl -> {size: (enc, dec)}
    for f in glob.glob(os.path.join(outdir, "*.csv")):
        impl = os.path.basename(f)[:-4]
        d = {}
        for line in open(f):
            line = line.strip()
            if not line:
                continue
            p = line.split(",")
            d[int(p[1])] = (float(p[2]), float(p[3]))
        data[impl] = d
    return data


def table(title, data, impls, idx):
    w = 17
    head = "size".ljust(9) + "".join(LABELS[i].rjust(w) for i in impls)
    print(title)
    print(head)
    print("-" * len(head))
    for size in SIZES:
        row = human(size).ljust(9)
        for i in impls:
            v = data[i].get(size)
            row += (f"{v[idx]:.1f}" if v else "-").rjust(w)
        print(row)
    print()


def main():
    outdir = sys.argv[1]
    data = load(outdir)
    impls = [i for i in ORDER if i in data]
    print("base64 throughput, MiB/s (best of 5 trials; higher is better)\n")
    table("== encode ==", data, impls, 0)
    table("== decode ==", data, impls, 1)


if __name__ == "__main__":
    main()
