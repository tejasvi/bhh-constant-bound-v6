/* ind_union.h: independent union area of unit disks (exposed arcs, Green's theorem) and the g table by dynamic
   programming, for test_components.c (names prefixed to avoid clashes with the checker source). */
#ifndef IND_UNION_H
#define IND_UNION_H
#include <math.h>
#include <stdlib.h>
#ifndef MAXK
#define MAXK 8
#endif
/* exact area of a union of unit disks via boundary arcs (Green's theorem) */
static int ind_cmpd(const void *a, const void *b) { double x = ((double *)a)[0], y = ((double *)b)[0]; return (x > y) - (x < y); }
static double ind_union_area(int n, const double *x, const double *y) {
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
    qsort(iv, m, sizeof iv[0], ind_cmpd);
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


/* 2g = 2p - n1 for connected graphs (p = minimum path cover by DP over (subset, last vertex)), 0 if disconnected;
   edge bit p <-> pair (i, j), i < j, lexicographic */
static int ind_g2(int kk, long long E) {
  int adj[8][8] = {{0}}, deg[8] = {0}, p = 0;
  for (int i = 0; i < kk; i++) for (int j = i + 1; j < kk; j++) { if ((E >> p) & 1) { adj[i][j] = adj[j][i] = 1; deg[i]++; deg[j]++; } p++; }
  int seen = 1, st[8], sp = 0; st[sp++] = 0;
  while (sp) { int v = st[--sp]; for (int w = 0; w < kk; w++) if (adj[v][w] && !(seen >> w & 1)) { seen |= 1 << w; st[sp++] = w; } }
  if (seen != (1 << kk) - 1) return 0;
  static int dp[1 << 8][8]; int full = (1 << kk) - 1;
  for (int mm = 0; mm <= full; mm++) for (int v = 0; v < kk; v++) dp[mm][v] = 1000;
  for (int v = 0; v < kk; v++) dp[1 << v][v] = 1;
  for (int mm = 1; mm <= full; mm++) for (int v = 0; v < kk; v++) {
    if (!(mm >> v & 1) || dp[mm][v] >= 1000) continue;
    for (int w = 0; w < kk; w++) if (!(mm >> w & 1)) { int c = dp[mm][v] + (adj[v][w] ? 0 : 1); if (c < dp[mm | 1 << w][w]) dp[mm | 1 << w][w] = c; }
  }
  int best = 1000; for (int v = 0; v < kk; v++) if (dp[full][v] < best) best = dp[full][v];
  int n1 = 0; for (int v = 0; v < kk; v++) if (deg[v] == 1) n1++;
  return 2 * best - n1;
}

#endif
