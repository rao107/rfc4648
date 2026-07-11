// base64 throughput via the Go stdlib `encoding/base64`.
//
// Mirrors LeanBase64.lean: same sizes, best-of-5 trials, one warmup. Emits CSV
// `go,<size>,<encode MiB/s>,<decode MiB/s>` on stdout.
package main

import (
	"crypto/rand"
	"encoding/base64"
	"fmt"
	"time"
)

var sizes = []int{16, 64, 256, 1024, 4096, 16384, 65536, 262144, 1048576}

const work = 1 << 21
const trials = 5

func best(iters int, fn func() int) int64 {
	var b int64 = -1
	for t := 0; t < trials; t++ {
		t0 := time.Now()
		cs := 0
		for i := 0; i < iters; i++ {
			cs ^= fn()
		}
		_ = cs
		d := time.Since(t0).Nanoseconds()
		if b < 0 || d < b {
			b = d
		}
	}
	return b
}

func mibps(size, iters int, nanos int64) float64 {
	return float64(size) * float64(iters) / (1 << 20) / (float64(nanos) / 1e9)
}

func main() {
	for _, size := range sizes {
		data := make([]byte, size)
		rand.Read(data)
		encoded := base64.StdEncoding.EncodeToString(data)
		iters := work / size
		if iters < 3 {
			iters = 3
		}
		enc := func() int { return len(base64.StdEncoding.EncodeToString(data)) }
		dec := func() int { b, _ := base64.StdEncoding.DecodeString(encoded); return len(b) }
		best(1, enc)
		best(1, dec)
		en := best(iters, enc)
		dn := best(iters, dec)
		fmt.Printf("go,%d,%.2f,%.2f\n", size, mibps(size, iters, en), mibps(size, iters, dn))
	}
}
