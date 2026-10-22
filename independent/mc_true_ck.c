/* mc_true_ck.c: Monte Carlo estimate of the Dong-Cao terms
     C_k = Gamma(k-1/2)/(2 k!) int_{(R^2)^{k-1}} g(G_1(y)) A(y)^{-(k-1/2)} dy,  y_0 = 0,
   g = p - n1/2 for connected unit-distance graphs (p: minimum number of vertex-disjoint paths covering the
   graph, n1: number of vertices of degree 1), 0 otherwise. A cross-check of the certified lower bounds
   (each certified C_k must lie below the estimate); not part of the proof.
   Proposal: random recursive tree (y_j uniform in the unit disk of a uniformly chosen earlier point), symmetrised over
   the orderings of the free points: int f = (k-1)! E_q[f / (q N)], N(y) = number of valid orderings.
   Build: gcc -O2 -o mc_true_ck mc_true_ck.c -lm      Usage: mc_true_ck K NSAMPLES SEED */
#include "ind_common.h"
/* number of orderings of the free points 1..n-1 in which each point is within 1 of 0 or an earlier point */
static int nvalid(int n, const double *x, const double *y) {
  int adj[MAXK][MAXK];
  for (int i = 0; i < n; i++) for (int j = 0; j < n; j++) { double dx = x[i] - x[j], dy = y[i] - y[j]; adj[i][j] = (i != j) && (dx * dx + dy * dy <= 1); }
  static long long cnt[1 << MAXK];
  int F = n - 1, full = (1 << F) - 1;   /* bit b <-> point b+1 */
  for (int m = 0; m <= full; m++) cnt[m] = 0;
  cnt[0] = 1;
  for (int m = 0; m <= full; m++) {
    if (!cnt[m]) continue;
    for (int b = 0; b < F; b++) {
      if (m >> b & 1) continue;
      int ok = adj[b + 1][0];
      for (int c = 0; c < F && !ok; c++) if ((m >> c & 1) && adj[b + 1][c + 1]) ok = 1;
      if (ok) cnt[m | 1 << b] += cnt[m];
    }
  }
  return (int)cnt[full];
}

int main(int argc, char **argv) {
  if (argc != 4 || atoi(argv[1]) < 3 || atoi(argv[1]) > MAXK || atoll(argv[2]) < 1) {
    fprintf(stderr, "usage: mc_true_ck K NSAMPLES SEED   (3 <= K <= %d, NSAMPLES >= 1)\n", MAXK); return 2;
  }
  int k = atoi(argv[1]); long long N = atoll(argv[2]); seed(strtoull(argv[3], 0, 10));
  double x[MAXK], y[MAXK], sum = 0, sum2 = 0; long long pos = 0;
  double fact_km1 = 1; for (int i = 2; i <= k - 1; i++) fact_km1 *= i;
  double sexp = k - 0.5;
  for (long long it = 0; it < N; it++) {
    x[0] = 0; y[0] = 0; double q = 1;
    for (int j = 1; j < k; j++) {
      int par = (int)(U() * j); if (par >= j) par = j - 1;
      double r = sqrt(U()), th = 2 * M_PI * U();
      x[j] = x[par] + r * cos(th); y[j] = y[par] + r * sin(th);
      int c = 0; for (int i = 0; i < j; i++) { double dx = x[j] - x[i], dy = y[j] - y[i]; if (dx * dx + dy * dy <= 1) c++; }
      q *= (double)c / (j * M_PI);
    }
    double g = gval(k, x, y), w = 0;
    if (g > 0) {
      double A = union_area(k, x, y);
      int Nv = nvalid(k, x, y);
      w = g * pow(A, -sexp) / (q * Nv);
      pos++;
    }
    sum += w; sum2 += w * w;
  }
  double mean = sum / N, var = sum2 / N - mean * mean;
  double kf = 1; for (int i = 2; i <= k; i++) kf *= i;
  double pref = tgamma(k - 0.5) / (2 * kf) * fact_km1;
  printf("k=%d N=%lld positive=%lld  C_k = %.7f +- %.7f\n", k, N, pos, pref * mean, pref * sqrt(var / N));
  return 0;
}
