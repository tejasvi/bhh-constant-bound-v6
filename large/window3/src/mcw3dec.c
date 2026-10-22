/* mcdec.c -- MC decomposition of the Dong-Cao terms C_k (float, exploration only).
 * Sampling as in ../../src/mc_ck.c (uniform labelled tree, child = parent + uniform point of unit disk),
 * weight W = Gamma(k-1/2)/(2 k!) pi^{k-1} k^{k-2} g / (tau A^s), E W = C_k (g = p - D).
 * Reports E[W * factor] for several restricted events / surrogate integrands.
 * usage: mcdec K N SEED
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <math.h>
#include <string.h>
#ifndef WIN
#define WIN 2
#endif
#ifndef WCERT
#define WCERT WIN
#endif
#ifndef WAREA
#define WAREA WIN
#endif
#define KMAX 12
static uint64_t rs[2];
static inline uint64_t rotl(const uint64_t x, int k) { return (x << k) | (x >> (64 - k)); }
static uint64_t next64(void) { uint64_t s0 = rs[0], s1 = rs[1], r = s0 + s1; s1 ^= s0;
  rs[0] = rotl(s0, 24) ^ s1 ^ (s1 << 16); rs[1] = rotl(s1, 37); return r; }
static double unif(void) { return (next64() >> 11) * 0x1.0p-53; }

static double union_area(int n, const double *x, const double *y) {
  double total = 0;
  for (int i = 0; i < n; i++) {
    double lo[KMAX], hi[KMAX]; int m = 0, covered = 0;
    for (int j = 0; j < n; j++) {
      if (j == i) continue;
      double dx = x[j] - x[i], dy = y[j] - y[i], d = sqrt(dx * dx + dy * dy);
      if (d >= 2) continue;
      if (d == 0) { if (j < i) { covered = 1; break; } else continue; }
      double phi = atan2(dy, dx), a = acos(d / 2);
      lo[m] = phi - a; hi[m] = phi + a; m++;
    }
    if (covered) continue;
    double L[2 * KMAX], H[2 * KMAX]; int q = 0;
    for (int t = 0; t < m; t++) {
      double a0 = lo[t], b0 = hi[t];
      while (a0 < 0) { a0 += 2 * M_PI; b0 += 2 * M_PI; }
      while (a0 >= 2 * M_PI) { a0 -= 2 * M_PI; b0 -= 2 * M_PI; }
      if (b0 <= 2 * M_PI) { L[q] = a0; H[q] = b0; q++; }
      else { L[q] = a0; H[q] = 2 * M_PI; q++; L[q] = 0; H[q] = b0 - 2 * M_PI; q++; }
    }
    for (int s = 1; s < q; s++) { double a0 = L[s], b0 = H[s]; int r = s - 1;
      while (r >= 0 && L[r] > a0) { L[r + 1] = L[r]; H[r + 1] = H[r]; r--; } L[r + 1] = a0; H[r + 1] = b0; }
    double cur = 0;
    for (int s = 0; s <= q; s++) {
      double a0 = (s < q) ? L[s] : 2 * M_PI;
      if (a0 > cur) { double t1 = cur, t2 = a0;
        total += 0.5 * ((t2 - t1) + x[i] * (sin(t2) - sin(t1)) - y[i] * (cos(t2) - cos(t1))); }
      if (s < q && H[s] > cur) cur = H[s];
    }
  }
  return total;
}
static int k; static double delta_g = 0;
static int adj[KMAX];
static int hp[1 << KMAX];
static long long nhp[1 << KMAX][KMAX];  /* number of Hamiltonian paths of G[mask] ending at v (directed, start anywhere) */
static int min_path_cover(void) {
  int full = (1 << k) - 1;
  for (int mask = 1; mask <= full; mask++) {
    if ((mask & (mask - 1)) == 0) { hp[mask] = mask; continue; }
    int ends = 0;
    for (int v = 0; v < k; v++) { if (!((mask >> v) & 1)) continue;
      int rest = mask & ~(1 << v); if (hp[rest] & adj[v]) ends |= 1 << v; }
    hp[mask] = ends;
  }
  static int pc[1 << KMAX]; pc[0] = 0;
  for (int mask = 1; mask <= full; mask++) {
    int low = mask & -mask, best = 99;
    for (int sub = mask; sub; sub = (sub - 1) & mask) { if (!(sub & low) || !hp[sub]) continue;
      int c = 1 + pc[mask & ~sub]; if (c < best) best = c; }
    pc[mask] = best;
  }
  return pc[full];
}
static long long count_ham_paths(void) { /* undirected count */
  int full = (1 << k) - 1;
  for (int mask = 1; mask <= full; mask++) for (int v = 0; v < k; v++) nhp[mask][v] = 0;
  for (int v = 0; v < k; v++) nhp[1 << v][v] = 1;
  for (int mask = 1; mask <= full; mask++) for (int v = 0; v < k; v++) {
    if (!nhp[mask][v]) continue;
    int nb = adj[v] & ~mask;
    while (nb) { int u = __builtin_ctz(nb); nb &= nb - 1; nhp[mask | (1 << u)][u] += nhp[mask][v]; }
  }
  long long s = 0; for (int v = 0; v < k; v++) s += nhp[full][v];
  return s / 2;
}
static int has_ham_cycle(void) { /* paths from vertex 0 */
  int full = (1 << k) - 1;
  static char dp[1 << KMAX][KMAX];
  memset(dp, 0, sizeof(dp)); dp[1][0] = 1;
  for (int mask = 1; mask <= full; mask += 2) for (int v = 0; v < k; v++) {
    if (!dp[mask][v]) continue;
    int nb = adj[v] & ~mask;
    while (nb) { int u = __builtin_ctz(nb); nb &= nb - 1; dp[mask | (1 << u)][u] = 1; }
  }
  for (int v = 1; v < k; v++) if (dp[full][v] && ((adj[v] >> 0) & 1)) return 1;
  return 0;
}
static long long spanning_trees(void) {
  long long M[KMAX][KMAX]; int n = k - 1;
  for (int i = 0; i < n; i++) for (int j = 0; j < n; j++) { int a = i + 1, b = j + 1;
    if (a == b) M[i][j] = __builtin_popcount(adj[a]); else M[i][j] = ((adj[a] >> b) & 1) ? -1 : 0; }
  long long prev = 1;
  for (int p = 0; p < n - 1; p++) {
    if (M[p][p] == 0) { int r = p + 1; while (r < n && M[r][p] == 0) r++; if (r == n) return 0;
      for (int j = 0; j < n; j++) { long long t = M[p][j]; M[p][j] = M[r][j]; M[r][j] = -t; } }
    for (int i = p + 1; i < n; i++) for (int j = p + 1; j < n; j++) M[i][j] = (M[i][j] * M[p][p] - M[i][p] * M[p][j]) / prev;
    prev = M[p][p];
  }
  long long d = M[n - 1][n - 1]; return d < 0 ? -d : d;
}

static unsigned char mt[1 << KMAX][KMAX][2];
static int min_turns(const double *x) {
  int full = (1 << k) - 1;
  for (int mask = 1; mask <= full; mask++) for (int v = 0; v < k; v++) mt[mask][v][0] = mt[mask][v][1] = 255;
  for (int v = 0; v < k; v++) mt[1 << v][v][0] = mt[1 << v][v][1] = 0;
  for (int mask = 1; mask <= full; mask++) for (int v = 0; v < k; v++) for (int d = 0; d < 2; d++) {
    int c = mt[mask][v][d]; if (c == 255) continue;
    int nb = adj[v] & ~mask;
    while (nb) { int u = __builtin_ctz(nb); nb &= nb - 1; int dn = (x[u] > x[v]) ? 0 : 1;
      int cn = c + (dn != d && __builtin_popcount(mask) > 1);
      if (cn < mt[mask | (1 << u)][u][dn]) mt[mask | (1 << u)][u][dn] = cn; }
  }
  int best = 255; for (int v = 0; v < k; v++) for (int d = 0; d < 2; d++) if (mt[full][v][d] < best) best = mt[full][v][d];
  return best;
}

static double A2(double x0, double y0, double x1, double y1) { double xs[2] = {x0, x1}, ys[2] = {y0, y1}; return union_area(2, xs, ys); }
static double A3(double x0, double y0, double x1, double y1, double x2, double y2) { double xs[3] = {x0, x1, x2}, ys[3] = {y0, y1, y2}; return union_area(3, xs, ys); }
static int adjp(const double *xs, const double *ys, int a, int b) { double dx = xs[a] - xs[b], dy = ys[a] - ys[b]; return dx * dx + dy * dy <= 1.0; }
/* local degree certificate: e has >= 2 neighbours among sorted positions within distance <= W of e */
static int cert(const double *xs, const double *ys, int e, int W) {
  int c = 0; for (int j = e - W; j <= e + W; j++) if (j >= 0 && j < k && j != e && adjp(xs, ys, e, j)) c++;
  return c >= 2;
}
int main(int argc, char **argv) {
  if (argc < 4) { fprintf(stderr, "usage: mcdec3 K N SEED\n"); return 1; }
  k = atoi(argv[1]); long long N = atoll(argv[2]); if (argc > 4) delta_g = atof(argv[4]);
  rs[0] = 0x9E3779B97F4A7C15ULL ^ atoll(argv[3]); rs[1] = 0xD1B54A32D192ED03ULL;
  for (int i = 0; i < 20; i++) next64();
  double s = k - 0.5;
  double pref = exp(lgamma(k - 0.5) - log(2.0) - lgamma(k + 1.0)) * pow(M_PI, k - 1) * pow(k, k - 2);
#define NQ 16
  double S[NQ] = {0}, S2[NQ] = {0};
  const char *nm[NQ] = {"all", "acc M", "acc TV", "acc TL", "acc any (exact g, exact A)", "acc any exact g, A_w2",
    "acc any ghat, A_w2", "conn+deg, A_w", "pure M ghat A_w2", "max(HP,conn), A_w", "conn+deg exact A", "fail but 1-turn HP", "", "", "", ""};
  double x[KMAX], y[KMAX];
  for (long long it = 0; it < N; it++) {
    int deg[KMAX], pr[KMAX];
    for (int i = 0; i < k; i++) deg[i] = 1;
    for (int i = 0; i < k - 2; i++) { pr[i] = (int)(unif() * k); deg[pr[i]]++; }
    int eu[KMAX], ev[KMAX], ne = 0;
    for (int i = 0; i < k - 2; i++) { int leaf = 0; while (deg[leaf] != 1) leaf++;
      eu[ne] = leaf; ev[ne] = pr[i]; ne++; deg[leaf]--; deg[pr[i]]--; }
    int a = -1, b = -1; for (int i = 0; i < k; i++) if (deg[i] == 1) { if (a < 0) a = i; else b = i; }
    eu[ne] = a; ev[ne] = b; ne++;
    int tadj[KMAX] = {0};
    for (int e = 0; e < ne; e++) { tadj[eu[e]] |= 1 << ev[e]; tadj[ev[e]] |= 1 << eu[e]; }
    int placed = 1, queue[KMAX], qh = 0, qt = 0; x[0] = 0; y[0] = 0; queue[qt++] = 0;
    while (qh < qt) { int u = queue[qh++]; int ch = tadj[u] & ~placed;
      while (ch) { int v = __builtin_ctz(ch); ch &= ch - 1; double r = sqrt(unif()), t = 2 * M_PI * unif();
        x[v] = x[u] + r * cos(t); y[v] = y[u] + r * sin(t); placed |= 1 << v; queue[qt++] = v; } }
    for (int i = 0; i < k; i++) adj[i] = 0;
    for (int i = 0; i < k; i++) for (int j = i + 1; j < k; j++) { double dx = x[i] - x[j], dy = y[i] - y[j];
      if (dx * dx + dy * dy <= 1.0) { adj[i] |= 1 << j; adj[j] |= 1 << i; } }
    int n1 = 0; for (int i = 0; i < k; i++) if (__builtin_popcount(adj[i]) == 1) n1++;
    int p = min_path_cover();
    double g = p - n1 / 2.0;
    double f[NQ] = {0};
    if (g > 0) {
      long long tau = spanning_trees();
      double A = union_area(k, x, y);
      double W = pref * g / ((double)tau * pow(A, s));
      f[0] = W;
      int o[KMAX]; for (int i = 0; i < k; i++) o[i] = i;
      for (int i = 1; i < k; i++) { int v = o[i], j = i - 1; while (j >= 0 && x[o[j]] > x[v]) { o[j + 1] = o[j]; j--; } o[j + 1] = v; }
      double xs[KMAX], ys[KMAX]; for (int i = 0; i < k; i++) { xs[i] = x[o[i]]; ys[i] = y[o[i]]; }
      /* SUBSET-construction automaton with uncertain adjacency tests (margin model of a cell discretisation):
         test (a,b), j = |a-b| increments: uncertain iff | |p_a-p_b| - 1 | < (j >= 2 ? j * DEL / 2 : 0)  (1-increment tests are grid-aligned).
         reachable set = intersection over hypotheses for the uncertain tests at each step; value = min over final hypotheses. */
      int Wn = WIN; double DEL = delta_g;
      int AS[KMAX][KMAX];
      for (int p1 = 0; p1 < k; p1++) for (int p2 = 0; p2 < k; p2++) {
        if (p1 == p2) { AS[p1][p2] = 0; continue; }
        double dd = sqrt((xs[p1] - xs[p2]) * (xs[p1] - xs[p2]) + (ys[p1] - ys[p2]) * (ys[p1] - ys[p2]));
        int j = abs(p1 - p2); double mg = (j >= 2) ? j * DEL / 2 : 0;
        AS[p1][p2] = (dd <= 1 - mg) ? 1 : ((dd > 1 + mg) ? 0 : -1);
      }
      int cert[KMAX]; for (int e = 0; e < k; e++) { int c = 0; for (int j = 0; j < k; j++) if (j != e && abs(j - e) <= WCERT && AS[e][j] == 1) c++; cert[e] = c >= 2; }
      double best = -1;
      { /* state code: mode, e1, oth, m (each +1) */
        #define ENC(MO, E1, OT, MM) ((((MO) * 16 + ((E1) + 1)) * 16 + ((OT) + 1)) * 16 + ((MM) + 1))
        static int cur[4096], ncur, nxt[4096], nn, tmp[4096], nt;
        ncur = 0; cur[ncur++] = ENC(0, 0, -1, -1);
        for (int i = 0; i < k - 1 && ncur > 0; i++) {
          int nx = i + 1;
          /* uncertain tests at this step: pairs (nx, j), j in [nx - Wn, i] */
          int ul[KMAX], nu = 0; for (int j = (nx - Wn > 0 ? nx - Wn : 0); j <= i; j++) if (AS[nx][j] < 0) ul[nu++] = j;
          int first = 1; nn = 0; double vmin = 1e9;
          for (int h = 0; h < (1 << nu); h++) {
            int adjh[KMAX]; for (int j = 0; j < k; j++) adjh[j] = (j >= nx - Wn && j <= i) ? (AS[nx][j] == 1) : 0;
            for (int q = 0; q < nu; q++) adjh[ul[q]] = (h >> q) & 1;
            nt = 0; double vbest = -1;
            for (int c = 0; c < ncur; c++) {
              int code = cur[c]; int mm_ = code % 16 - 1, ot = (code / 16) % 16 - 1, e1 = (code / 256) % 16 - 1, mode = code / 4096;
              int succ[8], ns = 0;
              if (mode == 0) {
                if (adjh[i]) succ[ns++] = ENC(0, e1, -1, -1);
                if (i >= 1 && e1 == 0 && nx <= Wn && adjh[0]) succ[ns++] = ENC(1, -1, i, -1);
                succ[ns++] = ENC(2, e1, i, nx);
              } else {
                if (adjh[i]) { if (nx - ot <= Wn) succ[ns++] = ENC(mode, e1, ot, mm_); if (mode == 1) succ[ns++] = ENC(0, ot, -1, -1); }
                if (nx - ot <= Wn && adjh[ot]) succ[ns++] = ENC(mode, e1, i, mm_);
              }
              for (int q = 0; q < ns; q++) {
                int sc = succ[q];
                if (nx == k - 1) { /* closure value under this hypothesis */
                  int mo = sc / 4096, e1n = (sc / 256) % 16 - 1, otn = (sc / 16) % 16 - 1, mmn = sc % 16 - 1; double gh = -1;
                  if (mo == 0) gh = 0.5 * (cert[e1n] + cert[k - 1]);
                  else if (mo == 1) gh = 0.5 * (cert[k - 1] + cert[otn]);
                  else if (k - 1 - otn <= Wn && (otn == i ? adjh[i] : (otn >= nx - Wn ? adjh[otn] : 0))) gh = 0.5 * (cert[e1n] + cert[mmn]);
                  if (gh > vbest) vbest = gh;
                } else { int dup = 0; for (int r = 0; r < nt; r++) if (tmp[r] == sc) { dup = 1; break; } if (!dup && nt < 4096) tmp[nt++] = sc; }
              }
            }
            if (nx == k - 1) { if (vbest < vmin) vmin = vbest; }
            else if (first) { memcpy(nxt, tmp, sizeof(int) * nt); nn = nt; first = 0; }
            else { int w2 = 0; for (int r = 0; r < nn; r++) { int keep = 0; for (int q = 0; q < nt; q++) if (tmp[q] == nxt[r]) { keep = 1; break; } if (keep) nxt[w2++] = nxt[r]; } nn = w2; }
          }
          if (nx == k - 1) { best = vmin; break; }
          memcpy(cur, nxt, sizeof(int) * nn); ncur = nn;
        }
      }
      /* connectivity + local degree bound: window-WIN edges connect all points -> g >= max(0, 1 - u/2), u = # points
         without 2 sure neighbours within sorted distance WCERT */
      double conn = 0;
      { int par[KMAX]; for (int a2 = 0; a2 < k; a2++) par[a2] = a2;
        for (int a2 = 0; a2 < k; a2++) for (int b2 = a2 + 1; b2 < k && b2 - a2 <= WIN; b2++) if (AS[a2][b2] == 1) {
          int ra = a2, rb = b2; while (par[ra] != ra) ra = par[ra]; while (par[rb] != rb) rb = par[rb]; if (ra != rb) par[ra] = rb; }
        int nroot = 0; for (int a2 = 0; a2 < k; a2++) if (par[a2] == a2) nroot++;
        int u = 0; for (int e = 0; e < k; e++) if (!cert[e]) u++;
        if (nroot == 1) conn = 1.0 - 0.5 * u; if (conn < 0) conn = 0; }
      if (conn > g + 1e-12) { fprintf(stderr, "BUG conn: %g > g %g\n", conn, g); exit(4); }
      double Aw2 = M_PI;
      for (int i = 1; i < k; i++) { int j0 = i - WAREA; if (j0 < 0) j0 = 0;
        Aw2 += union_area(i - j0 + 1, xs + j0, ys + j0) - union_area(i - j0, xs + j0, ys + j0); }
      double fw = W * pow(A / Aw2, s);
      f[7] = fw * conn / g; f[10] = W * conn / g;
      { double mx = conn; if (best > mx) mx = best; f[9] = fw * mx / g; }
      if (best >= 0) {
        if (best > g + 1e-12) { fprintf(stderr, "BUG nondet: ghat %g > g %g\n", best, g); exit(3); }
        f[4] = W; f[5] = fw; f[6] = f[5] * best / g;
      }
    }
    for (int i = 0; i < NQ; i++) { S[i] += f[i]; S2[i] += f[i] * f[i]; }
  }
  printf("k=%d N=%lld\n", k, N);
  for (int i = 0; i < 12; i++) { double mm = S[i] / N, e = sqrt((S2[i] / N - mm * mm) / N);
    printf("  %-30s %.6f +- %.6f (%.3f)\n", nm[i], mm, e, mm / (S[0] / N)); }
  return 0;
}
