/* leaf_truth.c: for leaves dumped by a dump-only copy of the checker (see patch_dump.py), the true integral
   int_{Q cap D} r2 g(G_1(y)) A(y)^{-(k-1/2)} dx over each leaf Q (D: r2 >= 0, eta_2 >= 0, xi_2 <= ... <= xi_{k-1}):
   tensor Gauss-Legendre for leaves with constant g and no order straddle, Monte Carlo otherwise; compares it with the
   checker's lower bound (a cross-check; not part of the proof).
   Build: gcc -O2 -o leaf_truth leaf_truth.c -lm      Usage: leaf_truth NGL NMC SEED < dump.txt */
#include "ind_common.h"
#define MINHITS 100
static uint64_t seed0;
static void gauss_legendre(int n, double *x, double *w) {
  for (int i = 0; i < n; i++) {
    double z = cos(M_PI * (i + 0.75) / (n + 0.5)), pp = 0;
    for (int it = 0; it < 100; it++) {
      double p1 = 1, p2 = 0;
      for (int j = 1; j <= n; j++) { double p3 = p2; p2 = p1; p1 = ((2 * j - 1) * z * p2 - (j - 1) * p3) / j; }
      pp = n * (z * p1 - p2) / (z * z - 1);
      double z1 = z; z = z1 - p1 / pp; if (fabs(z - z1) < 1e-15) break;
    }
    x[i] = z; w[i] = 2 / ((1 - z * z) * pp * pp);
  }
}
static double integrand(int k, const double *z) {
  double x[MAXK], y[MAXK];
  x[0] = 0; y[0] = 0; x[1] = z[0]; y[1] = 0;
  for (int j = 2; j < k; j++) { x[j] = z[2 * j - 3]; y[j] = z[2 * j - 2]; }
  int inD = (z[0] >= 0) && (k < 3 || y[2] >= 0);
  for (int j = 2; j + 1 < k && inD; j++) if (x[j] > x[j + 1]) inD = 0;
  if (!inD) return 0;
  double g = gval(k, x, y);
  return g > 0 ? z[0] * g * pow(union_area(k, x, y), -(k - 0.5)) : 0;
}
/* rare-event fallback for MC leaves with fewer than MINHITS sample points in the support of the integrand (own random
   stream; the main stream is restored, so the other leaves are unaffected): sample the leaf uniformly until MINHITS support
   points are found (at most 1000 NMC samples), take their bounding box H, enlarged by 10% of the leaf width per side and
   clipped to the leaf, and estimate with the defensive mixture q = (U(leaf) + U(H))/2. E_q[f/q] = int f for every H,
   since q >= 1/(2 vol) on the leaf. Returns the number of support points found (0: estimate unchanged). */
static long long rare_event(int k, int m, const double *lo, const double *hi, double vol, long long N, int ibox,
                            double *est, double *err, double *hfrac) {
  uint64_t save[4]; for (int i = 0; i < 4; i++) save[i] = s[i];
  seed(seed0 + 0x100000000ULL * (uint64_t) ibox);
  double hlo[16], hhi[16], z[16]; long long hits = 0;
  for (int d = 0; d < m; d++) { hlo[d] = hi[d]; hhi[d] = lo[d]; }
  for (long long it = 0; it < 1000 * N && hits < MINHITS; it++) {
    for (int d = 0; d < m; d++) z[d] = lo[d] + (hi[d] - lo[d]) * U();
    if (integrand(k, z) > 0) { hits++; for (int d = 0; d < m; d++) { if (z[d] < hlo[d]) hlo[d] = z[d]; if (z[d] > hhi[d]) hhi[d] = z[d]; } }
  }
  if (hits > 0) {
    double vh = 1;
    for (int d = 0; d < m; d++) {
      double w = 0.1 * (hi[d] - lo[d]); hlo[d] = fmax(lo[d], hlo[d] - w); hhi[d] = fmin(hi[d], hhi[d] + w); vh *= hhi[d] - hlo[d];
    }
    double sum = 0, sum2 = 0;
    for (long long it = 0; it < N; it++) {
      int fromH = U() < 0.5, inH = 1;
      for (int d = 0; d < m; d++) z[d] = fromH ? hlo[d] + (hhi[d] - hlo[d]) * U() : lo[d] + (hi[d] - lo[d]) * U();
      for (int d = 0; d < m; d++) if (z[d] < hlo[d] || z[d] > hhi[d]) inH = 0;
      double f = integrand(k, z), q = 0.5 / vol + (inH ? 0.5 / vh : 0), w = f / q;
      sum += w; sum2 += w * w;
    }
    double mean = sum / N; *est = mean; *err = sqrt(fmax(sum2 / N - mean * mean, 0) / N); *hfrac = vh / vol;
  }
  for (int i = 0; i < 4; i++) s[i] = save[i];
  return hits;
}
int main(int argc, char **argv) {
  if (argc != 4 || atoi(argv[1]) < 1 || atoi(argv[1]) > 64 || atoll(argv[2]) < 1) {
    fprintf(stderr, "usage: leaf_truth NGL NMC SEED < dump.txt   (1 <= NGL <= 64, NMC >= 1)\n"); return 2;
  }
  int ngl = atoi(argv[1]); long long N = atoll(argv[2]); seed0 = strtoull(argv[3], 0, 10); seed(seed0);
  double gx[64], gw[64]; gauss_legendre(ngl, gx, gw);
  char tag[16]; int k; int nbox = 0, nviol = 0, nrare = 0, nunres = 0; double worst = 0;
  while (scanf("%15s %d", tag, &k) == 2) {
    if (k < 3 || k > MAXK) { fprintf(stderr, "leaf_truth: k = %d out of range\n", k); return 1; }
    int m = 2 * k - 3; double lo[16], hi[16], lb, flt; int nstr, gmin, gmax;
    for (int d = 0; d < m; d++) if (scanf("%lf %lf", &lo[d], &hi[d]) != 2) return 1;
    if (scanf(" lb %lf flt %lf nstr %d gmin %d gmax %d", &lb, &flt, &nstr, &gmin, &gmax) != 5) return 1;
    double vol = 1; for (int d = 0; d < m; d++) vol *= hi[d] - lo[d];
    double est, err, hfrac = 0; int method; long long hits = -1, rhits = -1;
    if (gmin == gmax && nstr == 0) {
      method = 0; long long tot = 1; for (int d = 0; d < m; d++) tot *= ngl;
      double sum = 0, z[16];
      for (long long t = 0; t < tot; t++) {
        long long r = t; double w = 1;
        for (int d = 0; d < m; d++) { int i = r % ngl; r /= ngl; z[d] = lo[d] + (hi[d] - lo[d]) * (gx[i] + 1) / 2; w *= gw[i] * (hi[d] - lo[d]) / 2; }
        sum += w * integrand(k, z);
      }
      est = sum; err = 0;
    } else {
      method = 1; double sum = 0, sum2 = 0, z[16]; hits = 0;
      for (long long it = 0; it < N; it++) {
        for (int d = 0; d < m; d++) z[d] = lo[d] + (hi[d] - lo[d]) * U();
        double f = integrand(k, z); sum += f; sum2 += f * f; hits += f > 0;
      }
      double mean = sum / N; est = vol * mean; err = vol * sqrt(fmax(sum2 / N - mean * mean, 0) / N);
      if (hits < MINHITS && lb > 0) rhits = rare_event(k, m, lo, hi, vol, N, nbox + 1, &est, &err, &hfrac);
    }
    double ratio = est > 0 ? lb / est : (lb > 0 ? 1e9 : 0);
    int unres = rhits == 0, viol = !unres && (method == 0 ? (lb > est * (1 + 1e-9)) : (lb > est + 4 * err));
    nbox++; if (viol) nviol++; if (rhits >= 0) nrare++; if (unres) nunres++; else if (ratio > worst) worst = ratio;
    printf("box %d k=%d %s nstr=%d g=[%d,%d] lb=%.9e est=%.9e +- %.1e ratio=%.7f%s", nbox, k, method ? "MC" : "GL", nstr, gmin, gmax, lb, est, err, ratio, viol ? "  VIOLATION" : "");
    if (rhits > 0) printf("  RARE(%lld of %lld uniform samples in the support; mixture box %.2e of the leaf)", hits, N, hfrac);
    if (unres) printf("  UNRESOLVED(no support point in %lld samples)", 1001 * N);
    printf("\n");
    fflush(stdout);
  }
  printf("SUMMARY boxes=%d violations=%d max ratio lb/est=%.7f\n", nbox, nviol, worst);
  if (nrare) printf("RARE-EVENT FALLBACK: %d leaves, %d unresolved (excluded from the max ratio)\n", nrare, nunres);
  return 0;
}
