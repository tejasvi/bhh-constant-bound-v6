/* w3_tabletest.c -- Monte Carlo consistency test of the w3_arb.c tables (the certified source is #included unchanged).
 * The tables are built by calling the certified main with W3SLICE="0 1" W3SAVE=/dev/null (all triples, written to /dev/null),
 * then random entries are compared with uniform sample averages over their cells:
 *   abar2 >= E v2, LV3LO <= E A3, abar3 >= E v3 (each against the sample mean -/+ 5 standard errors), and the sure classes:
 *   S = 1 => |z + z'| <= 1 and T = 1 => |z_a + z_b + z_c| <= 1 at every sampled point (uniform and boundary samples).
 * usage: w3_tabletest N1 N2 NT NTH NENTRIES NSAMP SEED
 */
#define main cert_main
#include "w3_arb.c"
#undef main

static unsigned long long rs_ = 0x2545F4914F6CDD1DULL;
static double urand(void) { rs_ ^= rs_ << 13; rs_ ^= rs_ >> 7; rs_ ^= rs_ << 17; return (rs_ >> 11) * 0x1.0p-53; }
static void pt(int ir, int j, double u1, double u2, double *x, double *y) { sample_cell(ir, j, u1, u2, x, y); }
static void rnd_pt(int ir, int j, double *x, double *y) { pt(ir, j, urand(), urand(), x, y); }   /* uniform (area measure) */
static void bnd_pt(int ir, int j, double *x, double *y) {        /* boundary point: outer/inner arc or a radial side */
  double u1 = urand(), u2 = urand(); int e = (int)(urand() * 4);
  if (e == 0) u1 = 1; else if (e == 1) u1 = 0; else if (e == 2) u2 = 0; else u2 = 1;
  pt(ir, j, u1, u2, x, y);
}

int main(int argc, char **argv) {
  if (argc < 8) { fprintf(stderr, "usage: w3_tabletest N1 N2 NT NTH NENTRIES NSAMP SEED\n"); return 1; }
  setenv("W3SLICE", "0 1", 1); setenv("W3SAVE", "/dev/null", 1);
  char *cargv[8] = {argv[0], argv[1], argv[2], argv[3], "3", "1", "4", argv[4]};
  int rc = cert_main(8, cargv); if (rc) return rc;
  int NE = atoi(argv[5]), NS = atoi(argv[6]); rs_ ^= (unsigned long long)atoll(argv[7]) * 0x9E3779B97F4A7C15ULL;
  long long bad2 = 0, badl3 = 0, bad3 = 0, badS = 0, badT = 0, nS1 = 0, nT1 = 0, nlv = 0;
  double worst2 = 1e9, worstl3 = 1e9, worst3 = 1e9;
  for (int e = 0; e < NE; e++) {
    /* pair entry */
    int ir = (int)(urand() * NR), ir2 = (int)(urand() * NR), d = (int)(urand() * ND) - (NT - 1);
    size_t p = P2I(ir, ir2, d);
    double s1 = 0, s2 = 0, a1 = 0, a2 = 0; int sviol = 0;
    for (int q = 0; q < NS; q++) {
      double zx, zy, wx, wy; rnd_pt(ir, 0, &zx, &zy); rnd_pt(ir2, d, &wx, &wy);
      double X[3] = {-zx, 0, wx}, Y[3] = {-zy, 0, wy};
      double v = uarea_f(3, X, Y) - uarea_f(2, X, Y); s1 += v; s2 += v * v;
      double PX[3] = {-(zx + wx), -wx, 0}, PY[3] = {-(zy + wy), -wy, 0};
      double A3v = uarea_f(3, PX, PY); a1 += A3v; a2 += A3v * A3v;
      if ((zx + wx) * (zx + wx) + (zy + wy) * (zy + wy) > 1.0 + 1e-12) sviol = 1;
    }
    for (int q = 0; q < NS; q++) { double zx, zy, wx, wy; bnd_pt(ir, 0, &zx, &zy); bnd_pt(ir2, d, &wx, &wy);
      if ((zx + wx) * (zx + wx) + (zy + wy) * (zy + wy) > 1.0 + 1e-12) sviol = 1; }
    double m = s1 / NS, se = sqrt(fmax(s2 / NS - m * m, 0) / NS);
    double slack2 = ABAR2[p] - (m - 5 * se); if (slack2 < 0) bad2++; if ((ABAR2[p] - m) / (se + 1e-12) < worst2) worst2 = (ABAR2[p] - m) / (se + 1e-12);
    double ma = a1 / NS, sa = sqrt(fmax(a2 / NS - ma * ma, 0) / NS);
    if (LV3LO[p] > ma + 5 * sa) badl3++; if ((ma - LV3LO[p]) / (sa + 1e-12) < worstl3) worstl3 = (ma - LV3LO[p]) / (sa + 1e-12);
    if (SCL2[p]) { nS1++; if (sviol) badS++; }
    /* triple entry */
    int ia = (int)(urand() * NR), ib = (int)(urand() * NR), ic = (int)(urand() * NR);
    int dab = (int)(urand() * ND) - (NT - 1), dbc = (int)(urand() * ND) - (NT - 1);
    size_t t3 = T3I(ia, ib, ic, dab, dbc);
    double t1s = 0, t2s = 0; int tviol = 0;
    for (int q = 0; q < NS; q++) {
      double ax, ay, bx, by, cx, cy; rnd_pt(ia, 0, &ax, &ay); rnd_pt(ib, dab, &bx, &by); rnd_pt(ic, dab + dbc, &cx, &cy);
      double X[4] = {-(ax + bx), -bx, 0, cx}, Y[4] = {-(ay + by), -by, 0, cy};
      double v = uarea_f(4, X, Y) - uarea_f(3, X, Y); t1s += v; t2s += v * v;
      double sx = ax + bx + cx, sy = ay + by + cy; if (sx * sx + sy * sy > 1.0 + 1e-12) tviol = 1;
    }
    for (int q = 0; q < NS; q++) { double ax, ay, bx, by, cx, cy; bnd_pt(ia, 0, &ax, &ay); bnd_pt(ib, dab, &bx, &by); bnd_pt(ic, dab + dbc, &cx, &cy);
      double sx = ax + bx + cx, sy = ay + by + cy; if (sx * sx + sy * sy > 1.0 + 1e-12) tviol = 1; }
    double m3 = t1s / NS, se3 = sqrt(fmax(t2s / NS - m3 * m3, 0) / NS);
    if ((double)ABAR3[t3] < m3 - 5 * se3) bad3++;
    if (((double)ABAR3[t3] - m3) / (se3 + 1e-12) < worst3) worst3 = ((double)ABAR3[t3] - m3) / (se3 + 1e-12);
    if ((double)ABAR3[t3] < ABAR2[P2I(ib, ic, dbc)] - 1e-6) nlv++;
    if (SCL3[t3]) { nT1++; if (tviol) badT++; }
  }
  printf("TABLETEST grid %d %d %d entries %d samples %d: abar2 < mean-5se: %lld (min (abar2-mean)/se %.2f); LV3LO > mean+5se: %lld "
         "(min (mean-LV3LO)/se %.2f); abar3 < mean-5se: %lld (min (abar3-mean)/se %.2f; abar3 below abar2 in %lld); S=1 entries %lld with a "
         "violating sample: %lld; T=1 entries %lld with a violating sample: %lld\n",
         N1, N2, NT, NE, NS, bad2, worst2, badl3, worstl3, bad3, worst3, nlv, nS1, badS, nT1, badT);
  return (bad2 || badl3 || bad3 || badS || badT) ? 3 : 0;
}
