/* base64 throughput via OpenSSL libcrypto (EVP_EncodeBlock / EVP_DecodeBlock).
 *
 * Mirrors LeanBase64.lean: same sizes, best-of-5 trials, one warmup. Emits CSV
 * `c,<size>,<encode MiB/s>,<decode MiB/s>` on stdout.
 *
 * Build: gcc -O2 c_base64.c -lcrypto -o c_base64
 */
#include <openssl/evp.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <time.h>

static const int sizes[] = {16, 64, 256, 1024, 4096, 16384, 65536, 262144, 1048576};
#define NSIZES ((int)(sizeof(sizes) / sizeof(sizes[0])))
#define WORK (1 << 21)
#define TRIALS 5

static long now_ns(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (long)ts.tv_sec * 1000000000L + ts.tv_nsec;
}

int main(void) {
    /* Buffers sized for the largest input; reused across sizes. */
    int maxin = sizes[NSIZES - 1];
    unsigned char *in = malloc(maxin);
    unsigned char *enc = malloc(((maxin + 2) / 3) * 4 + 1);
    unsigned char *dec = malloc(((maxin + 2) / 3) * 3 + 3);
    if (!in || !enc || !dec) return 1;
    for (int i = 0; i < maxin; i++) in[i] = (unsigned char)rand();

    for (int s = 0; s < NSIZES; s++) {
        int size = sizes[s];
        int enclen = EVP_EncodeBlock(enc, in, size);  /* NUL-terminates, returns strlen */
        int iters = WORK / size;
        if (iters < 3) iters = 3;

        volatile uint64_t cs = 0;
        long benc = -1, bdec = -1;
        /* warmup + best-of-TRIALS, encode then decode */
        for (int t = 0; t <= TRIALS; t++) {
            long t0 = now_ns();
            for (int k = 0; k < (t == 0 ? 1 : iters); k++)
                cs ^= (uint64_t)EVP_EncodeBlock(enc, in, size);
            long d = now_ns() - t0;
            if (t > 0 && (benc < 0 || d < benc)) benc = d;
        }
        for (int t = 0; t <= TRIALS; t++) {
            long t0 = now_ns();
            for (int k = 0; k < (t == 0 ? 1 : iters); k++)
                cs ^= (uint64_t)EVP_DecodeBlock(dec, enc, enclen);
            long d = now_ns() - t0;
            if (t > 0 && (bdec < 0 || d < bdec)) bdec = d;
        }
        (void)cs;

        double emib = (double)size * iters / (1 << 20) / ((double)benc / 1e9);
        double dmib = (double)size * iters / (1 << 20) / ((double)bdec / 1e9);
        printf("c,%d,%.2f,%.2f\n", size, emib, dmib);
    }
    free(in);
    free(enc);
    free(dec);
    return 0;
}
