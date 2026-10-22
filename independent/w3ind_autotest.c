/* w3ind_autotest.c: (1) exhaustive: the encoding w3ind_auto.h equals the direct val(H_3) (union-find + degrees) on every
   pattern of the inputs N, S, T, k = 3..KMAX; (2) Lemma 1 over all graphs G on k <= 7 sorted vertices: val(H_3(G)) <= p(G) -
   n1(G)/2 for connected G, where H_3 = edges of G at sorted distance <= 3, and val = 0 for disconnected G; (3) state counts.
   Build: gcc -O2 w3ind_autotest.c -o w3ind_autotest     Usage: w3ind_autotest [KMAX] */
#include "w3ind_auto.h"
static int findp(int *p, int x) { while (p[x] != x) x = p[x] = p[p[x]]; return x; }
static int direct2(int k, const int *N, const int *S, const int *T) {      /* doubled val(H_3) */
  int par[32], deg[32]; for (int i = 0; i < k; i++) { par[i] = i; deg[i] = 0; }
  for (int i = 1; i < k; i++) {
    if (N[i]) { deg[i]++; deg[i - 1]++; par[findp(par, i)] = findp(par, i - 1); }
    if (i >= 2 && S[i]) { deg[i]++; deg[i - 2]++; par[findp(par, i)] = findp(par, i - 2); }
    if (i >= 3 && T[i]) { deg[i]++; deg[i - 3]++; par[findp(par, i)] = findp(par, i - 3); }
  }
  for (int i = 1; i < k; i++) if (findp(par, i) != findp(par, 0)) return 0;
  int u = 0; for (int i = 0; i < k; i++) if (deg[i] < 2) u++;
  return u >= 2 ? 0 : 2 - u;
}
static int enc2(int k, const int *N, const int *S, const int *T) {
  int st = a3_start;
  for (int i = 1; i < k; i++) { st = a3_trans[st][N[i]][i >= 2 ? S[i] : 0][i >= 3 ? T[i] : 0]; if (st < 0) return 0; }
  return a3_close2[st];
}
static int pcover(int n, unsigned adj[]) {                 /* minimum path cover, DP over (subset, last) */
  static int dp[1 << 8][8];
  int full = (1 << n) - 1;
  for (int m = 0; m <= full; m++) for (int v = 0; v < n; v++) dp[m][v] = 99;
  for (int v = 0; v < n; v++) dp[1 << v][v] = 1;
  for (int m = 1; m <= full; m++) for (int v = 0; v < n; v++) if ((m >> v & 1) && dp[m][v] < 99)
    for (int w = 0; w < n; w++) if (!(m >> w & 1)) { int c = dp[m][v] + !((adj[v] >> w) & 1); if (c < dp[m | 1 << w][w]) dp[m | 1 << w][w] = c; }
  int b = 99; for (int v = 0; v < n; v++) if (dp[full][v] < b) b = dp[full][v];
  return b;
}
int main(int argc, char **argv) {
  int KMAX = argc > 1 ? atoi(argv[1]) : 10;
  a3_build();
  printf("encoded states: %d (start %d)\n", a3_nst, a3_start);
  for (int k = 3; k <= KMAX; k++) {
    int nN = k - 1, nS = k - 2, nT = k - 3; long np = 1L << (nN + nS + nT), mism = 0, pos = 0;
    int N[32], S[32], T[32];
    for (long p = 0; p < np; p++) {
      memset(N, 0, sizeof N); memset(S, 0, sizeof S); memset(T, 0, sizeof T);
      int b = 0;
      for (int i = 1; i <= k - 1; i++) N[i] = (p >> b++) & 1;
      for (int i = 2; i <= k - 1; i++) S[i] = (p >> b++) & 1;
      for (int i = 3; i <= k - 1; i++) T[i] = (p >> b++) & 1;
      int a = direct2(k, N, S, T), c = enc2(k, N, S, T);
      if (a != c) { if (mism < 5) printf("k=%d p=%ld direct %d enc %d\n", k, p, a, c); mism++; }
      if (a) pos++;
    }
    printf("k=%2d: %ld input patterns (%ld with val > 0): encoded != direct %ld\n", k, np, pos, mism);
    fflush(stdout);
  }
  for (int k = 3; k <= 7; k++) {
    int ne = k * (k - 1) / 2, eu[32], ev[32], t = 0;
    for (int a = 0; a < k; a++) for (int b = a + 1; b < k; b++) { eu[t] = a; ev[t] = b; t++; }
    long viol = 0, conn = 0;
    for (long m = 0; m < (1L << ne); m++) {
      unsigned adj[8] = {0}; int deg[8] = {0}; int N[32] = {0}, S[32] = {0}, T[32] = {0};
      for (int e = 0; e < ne; e++) if (m >> e & 1) {
        adj[eu[e]] |= 1u << ev[e]; adj[ev[e]] |= 1u << eu[e]; deg[eu[e]]++; deg[ev[e]]++;
        int dd = ev[e] - eu[e];
        if (dd == 1) N[ev[e]] = 1; else if (dd == 2) S[ev[e]] = 1; else if (dd == 3) T[ev[e]] = 1;
      }
      int par[8]; for (int i = 0; i < k; i++) par[i] = i;
      for (int e = 0; e < ne; e++) if (m >> e & 1) par[findp(par, eu[e])] = findp(par, ev[e]);
      int c = 1; for (int i = 1; i < k; i++) if (findp(par, i) != findp(par, 0)) c = 0;
      int v2 = direct2(k, N, S, T), v2e = enc2(k, N, S, T);
      if (v2 != v2e) viol++;
      if (!c) { if (v2) viol++; continue; }
      conn++;
      int n1 = 0; for (int i = 0; i < k; i++) if (deg[i] == 1) n1++;
      if (v2 > 2 * pcover(k, adj) - n1) viol++;
    }
    printf("Lemma 1, k=%d: %ld graphs (%ld connected): violations %ld\n", k, 1L << ne, conn, viol);
    fflush(stdout);
  }
  /* reachable states by layer (inputs restricted to existing partners) */
  int cur[A3_MAXST] = {0}; cur[a3_start] = 1;
  for (int step = 1; step <= 40; step++) {
    int nx[A3_MAXST] = {0};
    for (int s = 0; s < a3_nst; s++) if (cur[s]) for (int N = 0; N < 2; N++) for (int S = 0; S < 2; S++) for (int T = 0; T < 2; T++) {
      if ((step < 2 && S) || (step < 3 && T)) continue;
      int t2 = a3_trans[s][N][S][T]; if (t2 >= 0) nx[t2] = 1;
    }
    memcpy(cur, nx, sizeof nx);
    if (step <= 4 || step == 40) { int c = 0; for (int s = 0; s < a3_nst; s++) c += cur[s]; printf("states reachable after step %d: %d\n", step, c); }
  }
  return 0;
}
