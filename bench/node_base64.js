// base64 throughput via the Node.js stdlib (native `Buffer` base64).
//
// Mirrors LeanBase64.lean: same sizes, best-of-5 trials, one warmup. Emits CSV
// `node,<size>,<encode MiB/s>,<decode MiB/s>` on stdout.
'use strict';
const crypto = require('crypto');

const SIZES = [16, 64, 256, 1024, 4096, 16384, 65536, 262144, 1048576];
const WORK = 1 << 21;
const TRIALS = 5;

function best(iters, fn, arg) {
  let b = null;
  for (let t = 0; t < TRIALS; t++) {
    const t0 = process.hrtime.bigint();
    let cs = 0;
    for (let i = 0; i < iters; i++) cs ^= fn(arg);
    const d = Number(process.hrtime.bigint() - t0);
    if (b === null || d < b) b = d;
  }
  return b;
}

const mibps = (size, iters, nanos) => (size * iters) / (1 << 20) / (nanos / 1e9);

const enc = (d) => d.toString('base64').length;
const dec = (s) => Buffer.from(s, 'base64').length;

for (const size of SIZES) {
  const data = crypto.randomBytes(size);
  const encoded = data.toString('base64');
  const iters = Math.max(3, Math.floor(WORK / size));
  best(1, enc, data);
  best(1, dec, encoded);
  const en = best(iters, enc, data);
  const dn = best(iters, dec, encoded);
  console.log(`node,${size},${mibps(size, iters, en).toFixed(2)},${mibps(size, iters, dn).toFixed(2)}`);
}
