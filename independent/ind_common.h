/* ind_common.h: shared routines of the independent cross-check programs (not part of the proof).
   xoshiro256** random numbers; exact area of a union of unit disks from the exposed boundary arcs (Green's theorem);
   minimum path cover p(G) by dynamic programming over (vertex subset, last vertex); g = p - n1/2 (n1: number of
   vertices of degree 1) for connected unit-distance graphs, 0 otherwise. */
#ifndef IND_COMMON_H
#define IND_COMMON_H
#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#include <stdint.h>
#define MAXK 8
static uint64_t s[4];
static inline uint64_t rotl(const uint64_t x, int k) { return (x << k) | (x >> (64 - k)); }
static uint64_t nxt(void) { const uint64_t r = rotl(s[1] * 5, 7) * 9; const uint64_t t = s[1] << 17;
  s[2] ^= s[0]; s[3] ^= s[1]; s[1] ^= s[2]; s[0] ^= s[3]; s[2] ^= t; s[3] = rotl(s[3], 45); return r; }
static double U(void) { return (nxt() >> 11) * 0x1.0p-53; }
static void seed(uint64_t x) { for (int i = 0; i < 4; i++) { x += 0x9E3779B97F4A7C15ULL; uint64_t z = x;
  z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9ULL; z = (z ^ (z >> 27)) * 0x94D049BB133111EBULL; s[i] = z ^ (z >> 31); } }

/* exact area of a union of unit disks via boundary arcs (Green's theorem) */
static int cmpd(const void *a, const void *b) { double x = ((double *)a)[0], y = ((double *)b)[0]; return (x > y) - (x < y); }
static double union_area(int n, const double *x, const double *y) {
  double A = 0;
  for (int i = 0; i < n; i++) {
    double iv[2 * MAXK][2]; int m = 0; int covered = 0;
    for (int j = 0; j < n; j++) {
      if (j == i) continue;
      double dx = x[j] - x[i], dy = y[j] - y[i], d = sqrt(dx * dx + dy * dy);
      if (d >= 2) continue;
      if (d == 0) { if (j < i) covered = 1; continue; }   /* coincident: keep only the first copy */
      double ph = atan2(dy, dx), hw = acos(d / 2);
      double a = ph - hw, b = ph + hw;                    /* covered arc of circle i */
      while (a < 0) { a += 2 * M_PI; b += 2 * M_PI; }
      while (a >= 2 * M_PI) { a -= 2 * M_PI; b -= 2 * M_PI; }
      if (b > 2 * M_PI) { iv[m][0] = a; iv[m][1] = 2 * M_PI; m++; iv[m][0] = 0; iv[m][1] = b - 2 * M_PI; m++; }
      else { iv[m][0] = a; iv[m][1] = b; m++; }
    }
    if (covered) continue;
    qsort(iv, m, sizeof iv[0], cmpd);
    /* exposed = [0, 2pi] minus union of iv */
    double cur = 0;
    for (int t = 0; t <= m; t++) {
      double s0 = (t < m) ? iv[t][0] : 2 * M_PI;
      if (s0 > cur) {   /* exposed arc [cur, s0] */
        double a = cur, b = s0;
        A += 0.5 * (x[i] * (sin(b) - sin(a)) - y[i] * (cos(b) - cos(a)) + (b - a));
      }
      if (t < m && iv[t][1] > cur) cur = iv[t][1];
    }
  }
  return A;
}

/* p(G) = minimum path cover via DP over (subset, last vertex): breaks counted */
static int path_cover(int n, const int adj[MAXK][MAXK]) {
  static int dp[1 << MAXK][MAXK];
  int full = (1 << n) - 1;
  for (int m = 0; m <= full; m++) for (int v = 0; v < n; v++) dp[m][v] = 1000;
  for (int v = 0; v < n; v++) dp[1 << v][v] = 1;           /* one path so far */
  for (int m = 1; m <= full; m++)
    for (int v = 0; v < n; v++) {
      if (!(m >> v & 1) || dp[m][v] >= 1000) continue;
      for (int w = 0; w < n; w++) {
        if (m >> w & 1) continue;
        int c = dp[m][v] + (adj[v][w] ? 0 : 1);
        if (c < dp[m | 1 << w][w]) dp[m | 1 << w][w] = c;
      }
    }
  int best = 1000;
  for (int v = 0; v < n; v++) if (dp[full][v] < best) best = dp[full][v];
  return best;
}

static double gval(int n, const double *x, const double *y) {
  int adj[MAXK][MAXK] = {{0}}; int deg[MAXK] = {0};
  for (int i = 0; i < n; i++) for (int j = i + 1; j < n; j++) {
    double dx = x[i] - x[j], dy = y[i] - y[j];
    if (dx * dx + dy * dy <= 1) { adj[i][j] = adj[j][i] = 1; deg[i]++; deg[j]++; }
  }
  /* connectivity */
  int seen = 1, stack[MAXK], sp = 0; stack[sp++] = 0;
  while (sp) { int v = stack[--sp]; for (int w = 0; w < n; w++) if (adj[v][w] && !(seen >> w & 1)) { seen |= 1 << w; stack[sp++] = w; } }
  if (seen != (1 << n) - 1) return 0;
  int n1 = 0; for (int i = 0; i < n; i++) if (deg[i] == 1) n1++;
  return path_cover(n, adj) - 0.5 * n1;
}


#endif
