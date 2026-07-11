#!/usr/bin/env bash
# Build and run the base64 throughput comparison across mainstream languages
# and the verified Lean codec, then print a comparison table.
#
# Each language program mirrors LeanBase64.lean's methodology (same sizes,
# best-of-5 trials, one warmup) and emits CSV `<impl>,<size>,<enc>,<dec>`.
#
# Usage: bench/run.sh [--no-lean]   (--no-lean skips the Lean build/run)
set -euo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
root="$(dirname "$here")"
# Keep artifacts so `compare.py` can be re-run without redoing the measurements.
out="$here/.last-run"
mkdir -p "$out"

run() {  # name, command...
  local name="$1"; shift
  if command -v "$1" >/dev/null 2>&1 || [ -x "$1" ]; then
    echo "  $name ..." >&2
    "$@" > "$out/$name.csv"
  else
    echo "  $name: toolchain not found, skipping" >&2
  fi
}

echo "Running base64 benchmarks (artifacts in $out):" >&2

run python  python3 "$here/py_base64.py"
run node    node    "$here/node_base64.js"

if command -v go >/dev/null 2>&1; then
  echo "  go ..." >&2
  ( cd "$here" && go run go_base64.go ) > "$out/go.csv"
else
  echo "  go: not found, skipping" >&2
fi

if command -v gcc >/dev/null 2>&1; then
  echo "  c (OpenSSL) ..." >&2
  gcc -O2 "$here/c_base64.c" -lcrypto -o "$out/c_base64"
  "$out/c_base64" > "$out/c.csv"
else
  echo "  c: gcc not found, skipping" >&2
fi

if command -v cargo >/dev/null 2>&1; then
  echo "  rust (base64 crate) ..." >&2
  ( cd "$here/rust" && cargo build --release -q )
  "$here/rust/target/release/rs_base64_bench" > "$out/rust.csv"
else
  echo "  rust: cargo not found, skipping" >&2
fi

if [ "${1:-}" != "--no-lean" ]; then
  echo "  lean (verified; builds first time) ..." >&2
  ( cd "$root" && lake exe bench ) > "$out/lean.csv"
else
  rm -f "$out/lean.csv"  # don't show a stale Lean column
fi

echo >&2
python3 "$here/compare.py" "$out"
