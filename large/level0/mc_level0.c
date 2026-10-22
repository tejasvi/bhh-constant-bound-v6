/* mc_level0.c -- independent float Monte Carlo of the LEVEL-0 quantity (reference only, not part of the proof):
 *   L_k = (Gamma(k-1/2)/2) int_{H^{k-1}} g_hat(z) (pi + sum_i u(|z_i|))^{-(k-1/2)} dz,   H = right half of the unit disk,
 *   g_hat = (1[|z_1+z_2| <= 1] + 1[|z_{k-2}+z_{k-1}| <= 1]) / 2,   u(d) = pi - 2 acos(d/2) + (d/2) sqrt(4 - d^2).
 * By the Laplace identity this equals (1/2) int t^{k-3/2} e^{-pi t} m(t)^{k-3} P2(t) dt (LEVEL0.md), so the rigorous
 * lower bounds must come out slightly below these estimates.
 * usage: mc_level0 N SEED KMAX
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <math.h>
static uint64_t s0 = 0x243F6A8885A308D3ULL, s1 = 0x13198A2E03707344ULL;
static inline uint64_t rotl(uint64_t x, int k) { return (x << k) | (x >> (64 - k)); }
static inline uint64_t nx(void) { uint64_t a = s0, b = s1, r = a + b; b ^= a; s0 = rotl(a, 24) ^ b ^ (b << 16); s1 = rotl(b, 37); return r; }
static inline double un(void) { return (nx() >> 11) * 0x1.0p-53; }
static double u(double d) { return M_PI - 2 * acos(d / 2) + (d / 2) * sqrt(4 - d * d); }
int main(int argc, char **argv) {
  long long N = atoll(argv[1]); s0 ^= (uint64_t)atoll(argv[2]) * 0x9E3779B97F4A7C15ULL; int KMAX = atoi(argv[3]);
  for (int i = 0; i < 16; i++) nx();
  double tot = 0;
  for (int k = 6; k <= KMAX; k++) {
    double s = k - 0.5, pref = exp(lgamma(s)) / 2 * pow(M_PI / 2, k - 1), sum = 0, sum2 = 0;
    double zx[64], zy[64];
    for (long long it = 0; it < N; it++) {
      double A = M_PI;
      for (int i = 1; i <= k - 1; i++) {        /* uniform in the right half-disk */
        double r = sqrt(un()), th = (un() - 0.5) * M_PI;
        zx[i] = r * cos(th); zy[i] = r * sin(th); A += u(r);
      }
      double L = ((zx[1] + zx[2]) * (zx[1] + zx[2]) + (zy[1] + zy[2]) * (zy[1] + zy[2]) <= 1) ? 1 : 0;
      double R = ((zx[k-2] + zx[k-1]) * (zx[k-2] + zx[k-1]) + (zy[k-2] + zy[k-1]) * (zy[k-2] + zy[k-1]) <= 1) ? 1 : 0;
      double w = 0.5 * (L + R) * pow(A, -s);
      sum += w; sum2 += w * w;
    }
    double m = pref * sum / N, se = pref * sqrt((sum2 / N - (sum / N) * (sum / N)) / N);
    printf("k=%2d: L_k ~ %.7e +- %.1e\n", k, m, se);
    tot += m;
  }
  printf("sum_{k=6..%d} L_k ~ %.7e\n", KMAX, tot);
  return 0;
}
