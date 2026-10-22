/* w3ind_geomtest.c: brute-force test of the support-function bounds of w3ind_geom.h (compiled in unchanged).
   For random polar cells (n = 2 or 3 cells, random rings and angular slots on a grid NT): the rigorous max of |sum| (h_max_up)
   must be >= the maximum over dense samples of the extreme points of the cells (inner corners and outer arc), and the
   distance lower bound -h_min_ub must be <= the minimum of |sum| over dense samples of the cells' convex hulls (points of the
   inner chord, radial sides, outer arc and interior). Also reports the tightness of both bounds.
   Usage: w3ind_geomtest NR1 NR2 NT NTRIALS SEED */
#include <stdint.h>
#define main w3ind_main_unused
#include "w3ind.c"
#undef main
static uint64_t gs = 88172645463325252ULL;
static double ur(void) { gs ^= gs << 13; gs ^= gs >> 7; gs ^= gs << 17; return (gs >> 11) * 0x1.0p-53; }
int main(int argc, char **argv) {
  if (argc != 6) return 2;
  NR1 = atoi(argv[1]); NR2 = atoi(argv[2]); NT = atoi(argv[3]); int NTR = atoi(argv[4]); gs ^= strtoull(argv[5], 0, 10) * 0x9E3779B97F4A7C15ULL;
  NSUB = 4; geom_init(); build_rings();
  pcell pc[3]; for (int i = 0; i < 3; i++) pcell_init(&pc[i]);
  mpfr_t hx, hn, x, y; mpfr_inits2(GPREC, hx, hn, x, y, (mpfr_ptr) 0);
  long badmax = 0, badmin = 0; double worst_max = -1, worst_min = -1, slack_max = 0, slack_min = 0;
  const int M = 400;
  for (int tr = 0; tr < NTR; tr++) {
    int n = 2 + (tr & 1), ir[3], k[3];
    for (int i = 0; i < n; i++) { ir[i] = (int) (ur() * NR); k[i] = (int) (ur() * (2 * NT)) - NT; set_cell(&pc[i], x, y, ir[i], k[i]); }
    h_max_up(hx, pc, n); h_min_ub(hn, pc, n);
    double up = mpfr_get_d(hx, MPFR_RNDU), dlo = -mpfr_get_d(hn, MPFR_RNDU);
    double dth = M_PI / NT;
    /* extreme points per cell: 2 inner corners + M points of the outer arc */
    double ex[3][M + 2], ey[3][M + 2];
    for (int i = 0; i < n; i++) {
      double r1 = mpfr_get_d(rr[ir[i]], MPFR_RNDN), r2 = mpfr_get_d(rr[ir[i] + 1], MPFR_RNDN), t1 = k[i] * dth;
      ex[i][0] = r1 * cos(t1); ey[i][0] = r1 * sin(t1); ex[i][1] = r1 * cos(t1 + dth); ey[i][1] = r1 * sin(t1 + dth);
      for (int q = 0; q < M; q++) { double th = t1 + dth * q / (M - 1); ex[i][q + 2] = r2 * cos(th); ey[i][q + 2] = r2 * sin(th); }
    }
    double bmax = 0;
    if (n == 2) { for (int a = 0; a < M + 2; a++) for (int b = 0; b < M + 2; b++) { double v = hypot(ex[0][a] + ex[1][b], ey[0][a] + ey[1][b]); if (v > bmax) bmax = v; } }
    else { for (int a = 0; a < M + 2; a += 4) for (int b = 0; b < M + 2; b += 4) for (int c = 0; c < M + 2; c += 4) { double v = hypot(ex[0][a] + ex[1][b] + ex[2][c], ey[0][a] + ey[1][b] + ey[2][c]); if (v > bmax) bmax = v; } }
    /* hull samples: random convex combinations of the extreme points (dense near the boundary) for the minimum */
    double bmin = 1e9;
    for (int s = 0; s < 20000; s++) {
      double sx = 0, sy = 0;
      for (int i = 0; i < n; i++) {
        int a = (int) (ur() * (M + 2)), b = (int) (ur() * (M + 2)); double w = ur(); if (s % 3 == 0) w = (w < 0.5 ? 0 : 1);
        sx += w * ex[i][a] + (1 - w) * ex[i][b]; sy += w * ey[i][a] + (1 - w) * ey[i][b];
      }
      double v = hypot(sx, sy); if (v < bmin) bmin = v;
    }
    if (bmax > up + 1e-12) { badmax++; if (bmax - up > worst_max) worst_max = bmax - up; }
    if (dlo > bmin + 1e-12) { badmin++; if (dlo - bmin > worst_min) worst_min = dlo - bmin; }
    slack_max += up - bmax; slack_min += bmin - (dlo > 0 ? dlo : 0);
  }
  printf("%d trials (n = 2, 3): max-bound violations %ld (worst %.2e), min-bound violations %ld (worst %.2e); mean slack max %.2e, min %.2e\n",
         NTR, badmax, worst_max, badmin, worst_min, slack_max / NTR, slack_min / NTR);
  return 0;
}
