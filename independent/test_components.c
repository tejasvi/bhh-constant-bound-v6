/* test_components.c: tests of the checker's components against independent code (a cross-check; not part of the proof).
   Includes the checker source (main renamed) and compares, for k = 3..6:
   (G) the g table and the pair-state minima own_g_bounds2 with an independent dynamic program;
   (R) rig_union_R (enlarged disks, 3e) and (A) rig_union with an independent union-area routine (arcs, Green);
   (E) ev_lb with direct evaluation; (B) Lemma V as implemented (rig_remainder, with the tangential cap) at sampled points
   of random boxes, half of them with a pair straddling tangency: pointwise, mean and second-moment bounds;
   (C) the staircase prob_strips with a fine quadrature; (D) cdf_xy with an independent closed form.
   Build: gcc -O2 -fopenmp -DCHK_SRC='"../checker/chk_ck14.c"' test_components.c -o test_components -lflint -lmpfr -lgmp -lm
   Expected: every count of mismatches / violations / differences is 0. */
#ifndef CHK_SRC
#define CHK_SRC "../checker/chk_ck14.c"
#endif
#define main chk_main_unused
#include CHK_SRC
#undef main
#include "ind_union.h"
static double ur(unsigned long long *st) { *st = *st * 6364136223846793005ULL + 1442695040888963407ULL; return (double)(*st >> 11) / 9007199254740992.0; }
static double dy(unsigned long long *st, double lo, double hi) { return lo + (hi - lo) * ldexp(floor(ur(st) * 1048576.0), -20); }
/* density of X - Y, X~U[a,b], Y~U[c,d] (b>a or d>c) at z; and CDF of the same via an independent formula */
static double tri_cdf(double a, double b, double c, double d, double z) {
  double w1 = b - a, w2 = d - c;
  if (w1 == 0 && w2 == 0) return (a - c <= z) ? 1 : 0;
  if (w1 == 0) { double t = (z - a + d) / w2; return t <= 0 ? 0 : t >= 1 ? 1 : t; }      /* P(Y >= a - z) */
  if (w2 == 0) { double t = (z - a + c) / w1; return t <= 0 ? 0 : t >= 1 ? 1 : t; }      /* P(X <= z + c) */
  /* numeric: integrate P(X <= z + y) over y */
  int n = 2000; double s = 0;
  for (int i = 0; i < n; i++) { double yv = c + (i + 0.5) * w2 / n; double t = (z + yv - a) / w1; s += t <= 0 ? 0 : t >= 1 ? 1 : t; }
  return s / n;
}


static double ind_cdf(double a, double b, double c, double d, double z) {
  double w1 = b - a, w2 = d - c;
  if (w1 == 0 && w2 == 0) return (a - c <= z) ? 1 : 0;
  if (w2 == 0) { double t = (z + c - a) / w1; return t <= 0 ? 0 : t >= 1 ? 1 : t; }
  if (w1 == 0) { /* P(a - Y <= z) = P(Y >= a - z) */ double t = (d - (a - z)) / w2; return t <= 0 ? 0 : t >= 1 ? 1 : t; }
  /* integrate h(y) = clamp((z + y - a)/w1, 0, 1) over [c, d]: breakpoints y1 = a - z, y2 = a - z + w1 */
  double y1 = a - z, y2 = a - z + w1, tot = 0;
  double lo = c > y1 ? c : y1, hi = d < y2 ? d : y2;       /* linear part */
  if (hi > lo) tot += ((z - a) * (hi - lo) + 0.5 * (hi * hi - lo * lo)) / w1;
  double l2 = c > y2 ? c : y2; if (d > l2) tot += d - l2;   /* h = 1 part */
  return tot / w2;
}
static int test_cdf(void) {
  unsigned long long st = 4242;
    double maxd = 0; int bad = 0, n = 0;
  for (int it = 0; it < 200000; it++) {
    double a = dy(&st, -2, 2), b = a + (it % 7 == 0 ? 0 : ldexp(1, -(int)(ur(&st) * 8))), c = dy(&st, -2, 2), d = c + (it % 11 == 0 ? 0 : ldexp(1, -(int)(ur(&st) * 8)));
    double z = (it % 3 == 0) ? 0 : dy(&st, -3, 3);
    arf_t zz; arf_init(zz); arf_set_d(zz, z);
    arb_t out; arb_init(out);
    cdf_xy(out, a, b, c, d, zz, RPREC);
    double ref = ind_cdf(a, b, c, d, z);
    double mid = arf_get_d(arb_midref(out), ARF_RND_NEAR), rad = mag_get_d(arb_radref(out));
    double e = fabs(mid - ref) - rad;
    if (e > maxd) maxd = e;
    if (e > 1e-14) bad++;
    n++;
    arb_clear(out); arf_clear(zz);
  }
  printf("(D) cdf_xy vs independent closed form: %d cases (incl. degenerate, z = 0 straddle case), %d differences > 1e-14 beyond the ball, max %.2e\n", n, bad, maxd);
  return bad;
}

int main(void) {
  unsigned long long st = 987654321ULL;
  slong prec = RPREC;
  for (int kk = 3; kk <= 6; kk++) {
    k = kk; m = 2 * k - 3; s_exp = k - 0.5;
    build_tables(); own_build_g(); init_proxy_circle();
    {   /* (G) g table and pair-state bounds own_g_bounds2 vs an independent DP */
      long long ng = 1LL << rnp, mism = 0;
      for (long long E = 0; E < ng; E++) if (g2own[E] != ind_g2(k, E)) mism++;
      int bad2 = 0, ntest = 0;
      for (int it = 0; it < 3000; it++) {
        int state[PMAX], ul[PMAX], nu, gmin, gmax, gp[PMAX], ga[PMAX];
        static int g2pair[PMAX * PMAX * 4];
        for (int p = 0; p < rnp; p++) { double u = ur(&st); state[p] = u < 0.4 ? 1 : (u < 0.6 ? 0 : 2); }
        int nund = 0; for (int p = 0; p < rnp; p++) if (state[p] == 2) nund++;
        if (nund > 10) continue;
        own_g_bounds2(state, &gmin, &gmax, gp, ga, ul, &nu, g2pair);
        /* brute force */
        int bmin = 1000, bmax = -1000, bp[PMAX], ba[PMAX], bpair[PMAX][PMAX][4];
        for (int p = 0; p < rnp; p++) { bp[p] = ba[p] = 1000; for (int q = 0; q < rnp; q++) for (int s4 = 0; s4 < 4; s4++) bpair[p][q][s4] = 1000; }
        int und[PMAX], nn = 0; long long base = 0;
        for (int p = 0; p < rnp; p++) { if (state[p] == 1) base |= 1LL << p; if (state[p] == 2) und[nn++] = p; }
        for (long long c = 0; c < (1LL << nn); c++) {
          long long E = base; for (int t = 0; t < nn; t++) if ((c >> t) & 1) E |= 1LL << und[t];
          int g = ind_g2(k, E);
          if (g < bmin) bmin = g; if (g > bmax) bmax = g;
          for (int t = 0; t < nn; t++) { int p = und[t]; if ((c >> t) & 1) { if (g < bp[p]) bp[p] = g; } else { if (g < ba[p]) ba[p] = g; } }
          for (int t1 = 0; t1 < nn; t1++) for (int t2 = t1 + 1; t2 < nn; t2++) { int s4 = 2 * (int)((c >> t1) & 1) + (int)((c >> t2) & 1); if (g < bpair[t1][t2][s4]) bpair[t1][t2][s4] = g; }
        }
        int ok = (gmin == bmin && gmax == bmax && nu == nn);
        for (int t = 0; t < nn && ok; t++) { int p = und[t]; if (gp[p] != bp[p] || ga[p] != ba[p] || ul[t] != p) ok = 0; }
        for (int t1 = 0; t1 < nn && ok; t1++) for (int t2 = t1 + 1; t2 < nn; t2++) for (int s4 = 0; s4 < 4; s4++) if (g2pair[(t1 * PMAX + t2) * 4 + s4] != bpair[t1][t2][s4]) ok = 0;
        if (!ok) bad2++;
        ntest++;
      }
      printf("k=%d (G) g table: %lld edge sets, %lld mismatches vs an independent DP; own_g_bounds2 (gmin, gmax, present/absent, pair states): %d random state vectors, %d mismatches\n", k, ng, mism, ntest, bad2);
    }
    {   /* (R) rig_union_R (3e enlarged disks) vs the independent union area, scaled: area(U B(c_i,R)) = R^2 area(U B(c_i/R, 1)) */
      int nR = 0, refused = 0; double maxd = 0;
      for (int it = 0; it < 3000; it++) {
        double xc[KMAX], yc[KMAX], sx[KMAX], sy[KMAX];
        xc[0] = yc[0] = 0;
        for (int i = 1; i < k; i++) { xc[i] = dy(&st, -1.5, 1.5); yc[i] = (i == 1) ? 0 : dy(&st, -1.5, 1.5); }
        if (it % 3 == 0 && k >= 3) { xc[2] = xc[1]; yc[2] = yc[1]; }                 /* identical centres */
        double Rd = 1 + ldexp(floor(ur(&st) * 1024), -12);                            /* R in [1, 1.25), dyadic */
        arf_t Rex; arf_init(Rex); arf_set_d(Rex, Rd);
        arb_t A; arb_init(A);
        if (rig_union_R(A, xc, yc, Rex, RPREC) != 0) { refused++; arb_clear(A); arf_clear(Rex); continue; }
        /* independent value: merge identical centres, scale */
        int n = 0; for (int i = 0; i < k; i++) { int dupl = 0; for (int j = 0; j < i; j++) if (xc[j] == xc[i] && yc[j] == yc[i]) dupl = 1; if (!dupl) { sx[n] = xc[i] / Rd; sy[n] = yc[i] / Rd; n++; } }
        double aind = Rd * Rd * ind_union_area(n, sx, sy);
        double mid = arf_get_d(arb_midref(A), ARF_RND_NEAR), rad = mag_get_d(arb_radref(A));
        double e = fabs(mid - aind) - rad - 1e-12; if (e > maxd) maxd = e;
        nR++;
        arb_clear(A); arf_clear(Rex);
      }
      printf("k=%d (R) rig_union_R: %d configs (1/3 with identical centres), %d refused; max |A_arb - A_ind| beyond the ball + 1e-12: %.2e\n", k, nR, refused, maxd);
    }
    {   /* (E) ev_lb vs double computation */
      int bad = 0;
      for (int it = 0; it < 20000; it++) {
        double q = ur(&st), fmn = ur(&st), fmx = fmn + ur(&st), val = ur(&st) * 2 - 0.5;
        arf_t aq, af, ag, av, out; arf_init(aq); arf_init(af); arf_init(ag); arf_init(av); arf_init(out);
        arf_set_d(aq, q); arf_set_d(af, fmn); arf_set_d(ag, fmx); arf_set_d(av, val);
        ev_lb(out, aq, af, ag, av);
        double ref = fmax(fmax(q * fmn, val - (1 - q) * fmx), 0), got = arf_get_d(out, ARF_RND_NEAR);
        if (fabs(ref - got) > 1e-12) bad++;
        arf_clear(aq); arf_clear(af); arf_clear(ag); arf_clear(av); arf_clear(out);
      }
      printf("k=%d (E) ev_lb: 20000 random inputs, %d differences from max(q fmin, val - (1-q) fmax, 0)\n", k, bad);
    }
    /* (A) */
    int failsA = 0, nA = 0; double maxdA = 0, maxdg = 0;
    for (int it = 0; it < 4000; it++) {
      double xc[KMAX], yc[KMAX];
      xc[0] = yc[0] = 0;
      for (int i = 1; i < k; i++) { xc[i] = dy(&st, -1.5, 1.5); yc[i] = (i == 1) ? 0 : dy(&st, -1.5, 1.5); }
      if (it % 5 == 1 && k >= 3) { double ang = 2 * M_PI * ur(&st); xc[2] = xc[1] + 2 * cos(ang) * (1 - 1e-9); yc[2] = 2 * sin(ang) * (1 - 1e-9); }
      if (it % 5 == 2 && k >= 3) { xc[2] = xc[1] + 1e-7; yc[2] = 1e-7; }
      if (it % 5 == 3 && k >= 4) { /* three circles through a common point */ double px = dy(&st, -0.5, 0.5), py = dy(&st, -0.5, 0.5);
        for (int i = 1; i < 4; i++) { double ang = 2 * M_PI * ur(&st); xc[i] = px + cos(ang); yc[i] = (i == 1) ? 0 : py + sin(ang); } xc[1] = px + sqrt(fmax(0, 1 - py * py)); }
      arb_t A, gxa[KMAX], gya[KMAX]; arb_init(A);
      for (int i = 0; i < k; i++) { arb_init(gxa[i]); arb_init(gya[i]); }
      if (rig_union(A, (arb_ptr) gxa, (arb_ptr) gya, xc, yc, prec) != 0) { failsA++; goto nextA; }
      nA++;
      double Am = ind_union_area(k, xc, yc);
      double mid = arf_get_d(arb_midref(A), ARF_RND_NEAR), rad = mag_get_d(arb_radref(A));
      double dA = fabs(mid - Am) - rad; if (dA > maxdA) maxdA = dA;
      for (int i = 1; i < k; i++) {
        double h = 1e-6, xp[KMAX], xm[KMAX];
        for (int t = 0; t < k; t++) { xp[t] = xc[t]; xm[t] = xc[t]; }
        xp[i] += h; xm[i] -= h;
        double fd = (ind_union_area(k, xp, yc) - ind_union_area(k, xm, yc)) / (2 * h);
        double gmid = arf_get_d(arb_midref(gxa[i]), ARF_RND_NEAR);
        if (fabs(gmid - fd) > maxdg && it % 5 != 1 && it % 5 != 2) maxdg = fabs(gmid - fd);
      }
    nextA:
      arb_clear(A); for (int i = 0; i < k; i++) { arb_clear(gxa[i]); arb_clear(gya[i]); }
    }
    printf("k=%d (A) union: %d configs evaluated, %d rigorous refusals; max |A_arb - A_ind| beyond the ball radius %.2e; max |grad_x - fd| %.2e\n", k, nA, failsA, maxdA, maxdg);
    /* (B) Lemma V */
    int nbox = 0, viol_pt = 0, viol_er = 0, viol_er2 = 0, skipped = 0; double worst_pt = -1e9, worst_er = -1e9, worst_er2 = -1e9;
    for (int it = 0; it < 1200; it++) {
      double xl[KMAX], xh[KMAX], yl[KMAX], yh[KMAX], xc[KMAX], yc[KMAX];
      double hwid = ldexp(1, -(2 + (int)(ur(&st) * 6)));          /* half widths 2^-2 .. 2^-7 */
      xl[0] = xh[0] = yl[0] = yh[0] = 0;
      double c1x = dy(&st, 0.05, 1.5); xl[1] = c1x - hwid * (0.25 + ur(&st)); xh[1] = xl[1] + 2 * hwid; yl[1] = yh[1] = 0;
      if (xl[1] < 0) { xl[1] = 0; xh[1] = 2 * hwid; }
      for (int j = 2; j < k; j++) { double cx = dy(&st, -1.5, 1.5), cy = dy(&st, -1.5, 1.5); xl[j] = cx; xh[j] = cx + 2 * hwid; yl[j] = cy; yh[j] = cy + 2 * hwid; }
      if (it % 2 == 1) {     /* every other box: a pair straddling tangency (d ~ 2) */
        double ang = 2 * M_PI * ur(&st), dd = 2 + (ur(&st) - 0.5) * 4 * hwid;
        double cx = 0.5 * (xl[1] + xh[1]) + dd * cos(ang), cy = dd * sin(ang);
        cx = ldexp(floor(ldexp(cx, 20)), -20); cy = ldexp(floor(ldexp(cy, 20)), -20);
        xl[2] = cx - hwid; xh[2] = cx + hwid; yl[2] = cy - hwid; yh[2] = cy + hwid;
        if (k >= 4) { double a3 = 2 * M_PI * ur(&st), d3 = 2 + (ur(&st) - 0.5) * 4 * hwid; double x3 = ldexp(floor(ldexp(d3 * cos(a3), 20)), -20), y3 = ldexp(floor(ldexp(d3 * sin(a3), 20)), -20);
          xl[3] = x3 - hwid; xh[3] = x3 + hwid; yl[3] = y3 - hwid; yh[3] = y3 + hwid; }
      }
      for (int i = 0; i < k; i++) { xc[i] = 0.5 * (xl[i] + xh[i]); yc[i] = 0.5 * (yl[i] + yh[i]); }
      arb_t d2mn[PMAX], d2mx[PMAX]; arf_t a1, a2; arf_init(a1); arf_init(a2);
      for (int p = 0; p < rnp; p++) { arb_init(d2mn[p]); arb_init(d2mx[p]); exact_d2(a1, a2, rpi[p], rpj[p], xl, xh, yl, yh); arb_set_arf(d2mn[p], a1); arb_set_arf(d2mx[p], a2); }
      arf_clear(a1); arf_clear(a2);
      arb_t A, gxa[KMAX], gya[KMAX], Rmax, Er, sEr2; int nv[PMAX];
      arb_init(A); arb_init(Rmax); arb_init(Er); arb_init(sEr2);
      for (int i = 0; i < k; i++) { arb_init(gxa[i]); arb_init(gya[i]); }
      int okb = (rig_union(A, (arb_ptr) gxa, (arb_ptr) gya, xc, yc, prec) == 0) &&
                (rig_remainder(Rmax, Er, sEr2, nv, xl, xh, yl, yh, xc, yc, d2mn[0], d2mx[0], prec) == 0);
      if (!okb) { skipped++; goto nextB; }
      nbox++;
      {
        double Ac = arf_get_d(arb_midref(A), ARF_RND_NEAR), Rm = arf_get_d(arb_midref(Rmax), ARF_RND_NEAR) + mag_get_d(arb_radref(Rmax));
        double ErU = arf_get_d(arb_midref(Er), ARF_RND_NEAR) + mag_get_d(arb_radref(Er));
        double s2U = arf_get_d(arb_midref(sEr2), ARF_RND_NEAR) + mag_get_d(arb_radref(sEr2));
        double gxv[KMAX], gyv[KMAX];
        for (int i = 0; i < k; i++) { gxv[i] = arf_get_d(arb_midref(gxa[i]), ARF_RND_NEAR); gyv[i] = arf_get_d(arb_midref(gya[i]), ARF_RND_NEAR); }
        int NS = 20000; double s1 = 0, s1b = 0, s2 = 0, maxex = -1e9;
        for (int t = 0; t < NS; t++) {
          double x[KMAX], y[KMAX], lin = 0;
          for (int i = 0; i < k; i++) { x[i] = xl[i] + (xh[i] - xl[i]) * ur(&st); y[i] = yl[i] + (yh[i] - yl[i]) * ur(&st); lin += gxv[i] * (x[i] - xc[i]) + gyv[i] * (y[i] - yc[i]); }
          double Ay = ind_union_area(k, x, y), ex = Ay - Ac - lin;
          if (ex - Rm > maxex) maxex = ex - Rm;
          s1 += ex; s1b += ex * ex; double pp = ex > 0 ? ex : 0; s2 += pp * pp;
        }
        double m1 = s1 / NS, m2 = s2 / NS, se1 = sqrt(fmax(s1b / NS - m1 * m1, 0) / NS);
        if (maxex > 1e-10) viol_pt++;
        if (maxex > worst_pt) worst_pt = maxex;
        double rel1 = m1 - ErU - 4 * se1, rel2 = sqrt(m2) - s2U;
        if (rel1 > worst_er) worst_er = rel1;
        if (rel2 > worst_er2) worst_er2 = rel2;
        if (rel1 > 0) viol_er++;
        if (rel2 > 1e-6) viol_er2++;
      }
    nextB:
      arb_clear(A); arb_clear(Rmax); arb_clear(Er); arb_clear(sEr2);
      for (int i = 0; i < k; i++) { arb_clear(gxa[i]); arb_clear(gya[i]); }
      for (int p = 0; p < rnp; p++) { arb_clear(d2mn[p]); arb_clear(d2mx[p]); }
    }
    printf("k=%d (B) Lemma V: %d boxes (%d refused), pointwise violations %d (max excess over Rmax %.3e), E-violations %d (max E[ex]-Er-4se %.3e), E2-violations %d (max sqrt E ex+^2 - sEr2 %.3e)\n",
           k, nbox, skipped, viol_pt, worst_pt, viol_er, worst_er, viol_er2, worst_er2);
    /* (C) staircase */
    int nc = 0, badC = 0; double worst_in = -1, worst_out = -1;
    for (int it = 0; it < 300; it++) {
      double xl[KMAX], xh[KMAX], yl[KMAX], yh[KMAX];
      for (int i = 0; i < k; i++) { double w = ldexp(1, -(1 + (int)(ur(&st) * 6))), cx = dy(&st, -1, 1), cy = dy(&st, -1, 1);
        xl[i] = cx; xh[i] = cx + w; yl[i] = cy; yh[i] = cy + w * (it % 4 == 0 ? 0 : 1); }
      xl[0] = xh[0] = yl[0] = yh[0] = 0; yl[1] = yh[1] = 0;
      int i = (int)(ur(&st) * k), j = (int)(ur(&st) * k); if (i == j) j = (i + 1) % k; if (i > j) { int t = i; i = j; j = t; }
      if (xh[i] - xl[i] == 0 && xh[j] - xl[j] == 0) continue;
      arf_t pin, pout; arf_init(pin); arf_init(pout);
      prob_strips(pin, pout, i, j, xl, xh, yl, yh, prec);
      double pi_lb = arf_get_d(pin, ARF_RND_UP), po_lb = arf_get_d(pout, ARF_RND_UP);
      /* true P(|Z| <= 1): integrate over Z_x with a fine midpoint rule using the exact CDF of Z_x */
      double zx0 = xl[i] - xh[j], zx1 = xh[i] - xl[j]; int n = 4000; double P = 0;
      for (int t = 0; t < n; t++) {
        double a = zx0 + (zx1 - zx0) * t / n, b = zx0 + (zx1 - zx0) * (t + 1) / n, xm = 0.5 * (a + b);
        double px = tri_cdf(xl[i], xh[i], xl[j], xh[j], b) - tri_cdf(xl[i], xh[i], xl[j], xh[j], a);
        if (fabs(xm) < 1) { double yb = sqrt(1 - xm * xm); P += px * (tri_cdf(yl[i], yh[i], yl[j], yh[j], yb) - tri_cdf(yl[i], yh[i], yl[j], yh[j], -yb - 1e-300)); }
      }
      double e1 = pi_lb - P, e2 = po_lb - (1 - P);
      if (e1 > worst_in) worst_in = e1; if (e2 > worst_out) worst_out = e2;
      if (e1 > 2e-3 || e2 > 2e-3) badC++;
      nc++;
      arf_clear(pin); arf_clear(pout);
    }
    printf("k=%d (C) staircase: %d cases, %d with pin > P + 2e-3 or pout > 1-P + 2e-3; max (pin - P) %.2e, max (pout - (1-P)) %.2e  [P by midpoint rule, error ~1e-4]\n", k, nc, badC, worst_in, worst_out);
    free(g2own);
  }
  printf("(D) run once after the k loop\n");
  return test_cdf() ? 1 : 0;
}
