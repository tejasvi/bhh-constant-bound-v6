/* chk_w3.c -- independent checker of the W3-conn bound (assembled from chk3/{header,helpers_from_chk_w2,chk_w3_main,chk_w3_tables,
 * chk_w3_rec,chk_w3_tail}.c by assemble.sh). See chk_w3_main.c for the description. Build:
 *   gcc -O3 -march=native -fopenmp -frounding-math -o chk_w3 chk_w3.c -lflint -lm
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <unistd.h>
#include <omp.h>
#include <fenv.h>
#include <flint/flint.h>
#include <flint/arf.h>
#include <flint/arb.h>
#include <flint/arb_hypgeom.h>
#define PREC 128
static arb_t PI_;
static void ucres(arb_t res, const arb_t d) {      /* u(d) for 0 <= d <= 2, pi for d >= 2 */
  arb_t h, s, two; arb_init(h); arb_init(s); arb_init(two); arb_set_ui(two, 2);
  if (arb_ge(d, two)) { arb_set(res, PI_); goto out; }
  arb_mul_2exp_si(h, d, -1);
  arb_one(s);
  if (!arb_le(h, s)) { /* ball straddles 2: use an enclosure of [u(d_lo), pi] via monotonicity (u increasing) */
    arf_t l; arf_init(l); arb_get_lbound_arf(l, d, PREC); arb_t dl; arb_init(dl); arb_set_arf(dl, l);
    arb_mul_2exp_si(h, dl, -1); arb_acos(s, h, PREC); arb_mul_2exp_si(s, s, 1); arb_sub(res, PI_, s, PREC);
    arb_mul(s, dl, dl, PREC); arb_neg(s, s); arb_add_ui(s, s, 4, PREC); arb_sqrt(s, s, PREC); arb_mul(s, s, h, PREC); arb_add(res, res, s, PREC);
    arb_union(res, res, PI_, PREC); arb_clear(dl); arf_clear(l); goto out; }
  arb_acos(s, h, PREC); arb_mul_2exp_si(s, s, 1); arb_sub(res, PI_, s, PREC);
  arb_mul(s, d, d, PREC); arb_neg(s, s); arb_add_ui(s, s, 4, PREC); arb_sqrt(s, s, PREC); arb_mul(s, s, h, PREC); arb_add(res, res, s, PREC);
out:
  arb_clear(h); arb_clear(s); arb_clear(two);
}

/* union area of n <= 4 unit disks with ball centres (tiny radii): arc complement with decided orderings; returns 0 or -1.
   (n = 3 for W = 2; n = 4 is the 4-disk union needed by a window-3 extension.) */
static int union_n(int n, arb_t A, arb_srcptr X, arb_srcptr Y) {
  arb_t twopi, dx, dy, d2, d, ph, al, lo, hi, t, s1, c1, s2, c2, four, zero;
  arb_init(twopi); arb_init(dx); arb_init(dy); arb_init(d2); arb_init(d); arb_init(ph); arb_init(al); arb_init(lo); arb_init(hi);
  arb_init(t); arb_init(s1); arb_init(c1); arb_init(s2); arb_init(c2); arb_init(four); arb_init(zero);
  arb_mul_2exp_si(twopi, PI_, 1); arb_set_ui(four, 4); arb_zero(zero);
  int ret = 0; arb_zero(A);
  for (int i = 0; i < n; i++) {
    arb_t S[8], E[8]; int ns = 0, E2pi[8] = {0, 0, 0, 0, 0, 0, 0, 0};
    for (int q = 0; q < 8; q++) { arb_init(S[q]); arb_init(E[q]); }
    for (int j = 0; j < n; j++) {
      if (j == i) continue;
      arb_sub(dx, X + j, X + i, PREC); arb_sub(dy, Y + j, Y + i, PREC);
      arb_sqr(d2, dx, PREC); arb_sqr(t, dy, PREC); arb_add(d2, d2, t, PREC);
      if (arb_ge(d2, four)) continue;
      if (!arb_lt(d2, four) || arb_contains_zero(d2)) { ret = -1; break; }
      arb_sqrt(d, d2, PREC); arb_atan2(ph, dy, dx, PREC); arb_mul_2exp_si(t, d, -1); arb_acos(al, t, PREC);
      arb_sub(lo, ph, al, PREC); arb_add(hi, ph, al, PREC);
      /* normalise lo into [0, 2pi) (decided), split wrap */
      for (int it = 0; it < 3; it++) { if (arb_lt(lo, zero)) { arb_add(lo, lo, twopi, PREC); arb_add(hi, hi, twopi, PREC); } }
      if (!arb_is_nonnegative(lo) || !arb_lt(lo, twopi)) { ret = -1; break; }
      if (arb_le(hi, twopi)) { arb_set(S[ns], lo); arb_set(E[ns], hi); ns++; }
      else if (arb_gt(hi, twopi)) { arb_set(S[ns], lo); arb_set(E[ns], twopi); E2pi[ns] = 1; ns++; arb_zero(S[ns]); arb_sub(E[ns], hi, twopi, PREC); ns++; }
      else { ret = -1; break; }
    }
    if (ret) { for (int q = 0; q < 8; q++) { arb_clear(S[q]); arb_clear(E[q]); } break; }
    /* sort by start with decided comparisons */
    for (int a = 1; a < ns; a++) for (int b = a; b > 0; b--) {
      if (arb_lt(S[b], S[b - 1])) { arb_swap(S[b], S[b - 1]); arb_swap(E[b], E[b - 1]); int tf = E2pi[b]; E2pi[b] = E2pi[b - 1]; E2pi[b - 1] = tf; }
      else if (!arb_ge(S[b], S[b - 1])) { ret = -1; }
    }
    if (ret) { for (int q = 0; q < 8; q++) { arb_clear(S[q]); arb_clear(E[q]); } break; }
    /* walk: exposed gaps between the running cover end and the next start (decided comparisons) */
    arb_t cur, Ai; arb_init(cur); arb_init(Ai); arb_zero(cur); arb_zero(Ai);
    int cur2pi = 0;   /* the running cover end is the symbolic endpoint 2 pi (from a wrap split) */
    for (int q = 0; q <= ns && !ret && !cur2pi; q++) {
      if (q == ns) {   /* final gap [cur, 2 pi] */
        if (arb_lt(cur, twopi)) {
          arb_sin_cos(s1, c1, cur, PREC); arb_sin_cos(s2, c2, twopi, PREC);
          arb_sub(t, twopi, cur, PREC);
          arb_sub(d, s2, s1, PREC); arb_mul(d, d, X + i, PREC); arb_add(t, t, d, PREC);
          arb_sub(d, c2, c1, PREC); arb_mul(d, d, Y + i, PREC); arb_sub(t, t, d, PREC);
          arb_mul_2exp_si(t, t, -1); arb_add(Ai, Ai, t, PREC);
        } else ret = -1;
        break;
      }
      if (arb_gt(S[q], cur)) {
        /* gap [cur, S[q]]: (1/2) [(b-a) + x (sin b - sin a) - y (cos b - cos a)] */
        arb_sin_cos(s1, c1, cur, PREC); arb_sin_cos(s2, c2, S[q], PREC);
        arb_sub(t, S[q], cur, PREC);
        arb_sub(d, s2, s1, PREC); arb_mul(d, d, X + i, PREC); arb_add(t, t, d, PREC);
        arb_sub(d, c2, c1, PREC); arb_mul(d, d, Y + i, PREC); arb_sub(t, t, d, PREC);
        arb_mul_2exp_si(t, t, -1); arb_add(Ai, Ai, t, PREC);
      } else if (!arb_le(S[q], cur)) ret = -1;
      if (E2pi[q]) cur2pi = 1;
      else if (arb_gt(E[q], cur)) arb_set(cur, E[q]);
      else if (!arb_le(E[q], cur)) ret = -1;
    }
    if (!ret) arb_add(A, A, Ai, PREC);
    arb_clear(cur); arb_clear(Ai);
    for (int q = 0; q < 8; q++) { arb_clear(S[q]); arb_clear(E[q]); }
    if (ret) break;
  }
  arb_clear(twopi); arb_clear(dx); arb_clear(dy); arb_clear(d2); arb_clear(d); arb_clear(ph); arb_clear(al); arb_clear(lo); arb_clear(hi);
  arb_clear(t); arb_clear(s1); arb_clear(c1); arb_clear(s2); arb_clear(c2); arb_clear(four); arb_clear(zero);
  return ret;
}

/* ================= directed-rounding helpers (W2 review note 5) ================= */
__attribute__((noinline)) static double ddiv(double a, double b) { return a / b; }
static double Q3N, Q10N;   /* 1/3 and 1/10 rounded to nearest (computed at start-up in the default mode) */
__attribute__((noinline)) static int rounding_selftest(int mode) {
  if (mode == FE_DOWNWARD) return ddiv(1.0, 10.0) < Q10N && ddiv(1.0, 3.0) == Q3N;
  if (mode == FE_UPWARD) return ddiv(1.0, 3.0) > Q3N && ddiv(1.0, 10.0) == Q10N;
  if (mode == FE_TONEAREST) return ddiv(1.0, 3.0) == Q3N && ddiv(1.0, 10.0) == Q10N;
  return 0;
}
__attribute__((noinline)) static int rounding_selftest_all(void) {
  int ok = 1, saved = fegetround();
  Q3N = ddiv(1.0, 3.0); Q10N = ddiv(1.0, 10.0);
  fesetround(FE_DOWNWARD); ok &= rounding_selftest(FE_DOWNWARD);
  fesetround(FE_UPWARD); ok &= rounding_selftest(FE_UPWARD);
  fesetround(FE_TONEAREST); ok &= rounding_selftest(FE_TONEAREST);
  fesetround(saved);
  return ok;
}
/* libm calls in nearest mode, results widened by 2^-40 (glibc exp/log errors < 1 ulp); caller's mode is restored */
static double exp_lo(double x) { int m = fegetround(); fesetround(FE_TONEAREST); double y = exp(x); fesetround(FE_DOWNWARD); y = y * (1.0 - ldexp(1.0, -40)); fesetround(m); return y; }
static double log_lo(double x) { int m = fegetround(); fesetround(FE_TONEAREST); double y = log(x); fesetround(FE_DOWNWARD); y = y - (fabs(y) * ldexp(1.0, -40) + ldexp(1.0, -1000)); fesetround(m); return y; }
static double log_hi(double x) { int m = fegetround(); fesetround(FE_TONEAREST); double y = log(x); fesetround(FE_UPWARD); y = y + (fabs(y) * ldexp(1.0, -40) + ldexp(1.0, -1000)); fesetround(m); return y; }
/* E ln 2 bounds: LN2_LO < ln 2 < LN2_HI */
static double elog2_lo(int E) { const double LN2_LO = 0.6931471805599453, LN2_HI = 0.6931471805599454; int m = fegetround(); fesetround(FE_DOWNWARD); double y = (E >= 0) ? E * LN2_LO : E * LN2_HI; fesetround(m); return y; }
static double elog2_hi(int E) { const double LN2_LO = 0.6931471805599453, LN2_HI = 0.6931471805599454; int m = fegetround(); fesetround(FE_UPWARD); double y = (E >= 0) ? E * LN2_HI : E * LN2_LO; fesetround(m); return y; }
/* lower bound of f(t) = t^{s-1} exp(-gam t + al) for t >= 0 (gam_hi >= gamma) */
static double flo(double t, double sm1, double gam_hi, double al) {
  if (t <= 0) return 0;
  int m = fegetround();
  double lt = log_lo(t);
  fesetround(FE_DOWNWARD);
  double ex = sm1 * lt;                       /* sm1 > 0: lower bound */
  double gt; fesetround(FE_UPWARD); gt = gam_hi * t; fesetround(FE_DOWNWARD);
  ex = (ex - gt) + al;
  double y = exp_lo(ex);
  fesetround(m);
  return y;
}

/* ================= chk_w3: independent checker of the window-3 connectivity bound (spec w3/W3.md) =================
 * Written from the specification only (w3_arb.c not read). Differences from the main evaluator, by design:
 *  - every distance range and the S/T classes come from an exact support-function computation over the convex hulls of the
 *    polar cells: max_psi sum_s h_s(psi) (piecewise sinusoids; the bound K + |(A,B)| is used whenever the critical angle may lie
 *    in a piece) and dist(0, K) = max(0, -min_psi sum_s h_s(psi)) (any psi gives a valid lower bound). No pentagons, no Lemma 4.
 *  - union areas by union_n (chk_w2: arc complement in arb, every ordering decided, else fallback), n = 3 and 4;
 *  - Lemma V (BOUNDS 3a) with the exact linear structure of the displacements: per pair A = |d_p| + |d_q| and the RELATIVE
 *    displacement B = |d_q - d_p| = |sum_s beta_s dz_s|, E[AB] <= sqrt(E A^2) sqrt(E B^2) (Cauchy-Schwarz), E B^2 = sum beta_s^2 m_s
 *    (independent, mean-zero increments), E A^2 <= (sum_s a_s sqrt(m_s))^2 (Minkowski);
 *  - E[A3] lower bound = max(two-sided Lemma V, pi + E u(|z_b|)_lo, pi + E u(|z_a|)_lo, pi + u(min |z_a + z_b|));
 *  - its own window-3 conn automaton written from Lemma 1;
 *  - recursion with directed rounding: pass 0 in FE_DOWNWARD with kernels rounded down, pass 1 in FE_UPWARD with kernels rounded
 *    up (no a priori floating-point analysis), dense F[current][previous][state], no mirror trick;
 *  - t-integral: on each grid interval the best of (a) Phi(t_{j+1}) (Phi decreasing), (b) the extension of the chord through
 *    (t_{j-1}, t_j) and (c) the extension of the chord through (t_{j+1}, t_{j+2}), all valid lower bounds of log Phi because
 *    Phi^disc is a positive combination of exponentials in t (log-convex); slopes from the [lower, upper] pass values with the
 *    orientation that keeps each line below log Phi; each piece int t^{s-1} e^{-(pi - beta) t + alpha} is bounded below by
 *    sum_m w sqrt(f(a_m) f(b_m)), valid because the integrand is log-concave in t; double with directed rounding.
 * usage:
 *   chk_w3 N1 N2 NT DTL T KMAX NTH                 full run (tables, recursion for all t_j, t-integral)
 *   env CHK3SLICE="s n" CHK3SAVE=file              compute triple slice s of n, save, exit
 *   env CHK3LOAD="f1 f2 ..."                       load the triple table from slices
 *   env CHK3J="j0 j1"                              recursion only for t_j, j0 <= j <= j1; prints PHI lines
 *   chk_w3 --int N1 N2 NT DTL T KMAX < PHI         t-integral from PHI lines (lines: PHI k j pass mantissa(%a) exponent)
 */

/* ===== support functions of polar cells ===== */
typedef struct { double r1, r2, t1, t2; } PC;          /* {r e^{i th}: r1 <= r <= r2, t1 <= th <= t2}, t2 - t1 < pi */
#define SMARG 1e-11                                     /* covers double rounding (< 1e-14 here) and cell-boundary rounding */
static double wrap2pi(double x) { double y = fmod(x, 2 * M_PI); if (y < 0) y += 2 * M_PI; if (y >= 2 * M_PI) y -= 2 * M_PI; return y; }
static double angd(double psi, const PC *c) {          /* angular distance from psi to the arc [t1, t2], in [0, pi] */
  double m = 0.5 * (c->t1 + c->t2), hw = 0.5 * (c->t2 - c->t1);
  double d = fabs(remainder(psi - m, 2 * M_PI)) - hw;
  return d > 0 ? d : 0;
}
static double hsup(const PC *c, double psi) {          /* support function of the cell (= of its hull) in direction psi */
  double d = angd(psi, c);
  if (d <= 0) return c->r2;
  double cs = cos(d);
  return cs >= 0 ? c->r2 * cs : c->r1 * cs;
}
static double hsum(const PC *cs, int n, double psi) { double s = 0; for (int i = 0; i < n; i++) s += hsup(cs + i, psi); return s; }
static int inpiece(double q, double p0, double p1) { double qq = q; if (qq < p0 - 1e-9) qq += 2 * M_PI; return qq >= p0 - 1e-9 && qq <= p1 + 1e-9; }
/* dmax: rigorous upper bound of max |x| over K = hull(c_1) + ... + hull(c_n) (= max over the product of the cells);
   dmin: rigorous lower bound of min |x| over K (dist(0, K)). */
static void hrange(const PC *cs, int n, double *dmin, double *dmax) {
  double bp[40]; int nb = 0;
  for (int i = 0; i < n; i++) {
    double t1 = cs[i].t1, t2 = cs[i].t2, m = 0.5 * (t1 + t2);
    bp[nb++] = wrap2pi(t1); bp[nb++] = wrap2pi(t2); bp[nb++] = wrap2pi(t2 + M_PI / 2); bp[nb++] = wrap2pi(t1 - M_PI / 2);
    bp[nb++] = wrap2pi(m + M_PI);
  }
  for (int a = 1; a < nb; a++) { double v = bp[a]; int b = a - 1; while (b >= 0 && bp[b] > v) { bp[b + 1] = bp[b]; b--; } bp[b + 1] = v; }
  double mx = -1e300, mn = 1e300;
  for (int k = 0; k < nb; k++) {
    double p0 = bp[k], p1 = (k + 1 < nb) ? bp[k + 1] : bp[0] + 2 * M_PI;
    double f0 = hsum(cs, n, p0), f1 = hsum(cs, n, p1);
    if (f0 > mx) mx = f0; if (f1 > mx) mx = f1; if (f0 < mn) mn = f0; if (f1 < mn) mn = f1;
    if (!(p1 - p0 > 1e-13)) continue;
    double pm = 0.5 * (p0 + p1), K = 0, A = 0, B = 0;
    for (int i = 0; i < n; i++) {
      const PC *c = cs + i; double d = angd(pm, c);
      if (d <= 0) { K += c->r2; continue; }
      double e1 = fabs(remainder(pm - c->t1, 2 * M_PI)), e2 = fabs(remainder(pm - c->t2, 2 * M_PI));
      double te = (e1 < e2) ? c->t1 : c->t2, rho = (cos(d) >= 0) ? c->r2 : c->r1;
      A += rho * cos(te); B += rho * sin(te);
    }
    double R = hypot(A, B), psc = wrap2pi(atan2(B, A)), pan = wrap2pi(psc + M_PI);
    if (inpiece(psc, p0, p1)) { double up = K + R; if (up > mx) mx = up; }        /* K + R >= the piece's sinusoid everywhere */
    if (inpiece(pan, p0, p1)) { double fa = hsum(cs, n, pan); if (fa < mn) mn = fa; }  /* an achieved value: valid for dmin */
  }
  *dmax = mx + SMARG;
  double dm = -mn - SMARG; *dmin = dm > 0 ? dm : 0;
}

/* ===== Lemma V with correlated linear displacements (arb) ===== */
typedef struct { int p, q; double dmn, dmx; } LVP;       /* distance range of |P_q - P_p| along segments (already widened) */
/* centres P_j = sum_s al[j][s] z_s + const, increments z_s independent, uniform on cells with second moments mom[s] about their
   centroids; rounded centres Ct_j with |C_j - Ct_j| <= ej[j]. Returns 0 and E r (sum over pairs, two vertices each), or -1 if a pair
   with dmn < 2 has dmn <= 0. */
static int lemv_corr(arb_t out, int nv, const int al[][3], arb_srcptr mom, arb_srcptr ej, const LVP *pr, int npr) {
  arb_t sq[3], A2s, B2, EA, EB, EAB, cr, c0, t, u, w, four, one, two, pi, dmn, dmx, term;
  for (int s = 0; s < 3; s++) arb_init(sq[s]);
  arb_init(A2s); arb_init(B2); arb_init(EA); arb_init(EB); arb_init(EAB); arb_init(cr); arb_init(c0); arb_init(t); arb_init(u);
  arb_init(w); arb_init(four); arb_init(one); arb_init(two); arb_init(pi); arb_init(dmn); arb_init(dmx); arb_init(term);
  arb_set_ui(four, 4); arb_one(one); arb_set_ui(two, 2); arb_const_pi(pi, PREC);
  for (int s = 0; s < nv; s++) arb_sqrt(sq[s], mom + s, PREC);
  int ret = 0; arb_zero(out);
  for (int k = 0; k < npr; k++) {
    int p = pr[k].p, q = pr[k].q;
    if (pr[k].dmn >= 2) continue;
    if (!(pr[k].dmn > 0)) { ret = -1; break; }
    arb_set_d(dmn, pr[k].dmn); arb_set_d(dmx, pr[k].dmx);
    arb_add(EA, ej + p, ej + q, PREC); arb_zero(B2);
    for (int s = 0; s < nv; s++) {
      int a = abs(al[p][s]) + abs(al[q][s]), b = al[q][s] - al[p][s];
      if (a) { arb_mul_si(t, sq[s], a, PREC); arb_add(EA, EA, t, PREC); }
      if (b) { arb_mul_si(t, mom + s, b * b, PREC); arb_add(B2, B2, t, PREC); }
    }
    arb_sqrt(EB, B2, PREC); arb_add(EB, EB, ej + p, PREC); arb_add(EB, EB, ej + q, PREC);    /* sqrt(E B^2) */
    arb_mul(EAB, EA, EB, PREC);                                                                /* >= E[A B] */
    double dmaxd = pr[k].dmx;
    arb_sqr(w, dmx, PREC);
    if (dmaxd < 1.98 && arb_lt(w, four)) { arb_sub(t, four, w, PREC); arb_sqrt(t, t, PREC); arb_inv(cr, t, PREC); arb_zero(c0); }
    else {
      arb_zero(cr); arb_mul_2exp_si(t, dmx, -1);
      if (arb_lt(t, one)) arb_asin(u, t, PREC); else arb_mul_2exp_si(u, pi, -1);
      arb_mul_2exp_si(t, dmn, -1); arb_asin(w, t, PREC);
      arb_sub(c0, u, w, PREC); arb_mul_2exp_si(c0, c0, 1);
    }
    arb_div(term, EAB, dmn, PREC); arb_mul(t, pi, EA, PREC); arb_min(term, term, t, PREC);   /* tangential */
    arb_addmul(term, cr, EAB, PREC); arb_addmul(term, c0, EA, PREC);                            /* radial */
    arb_mul_2exp_si(term, term, 1);                                                             /* two vertices */
    arb_add(out, out, term, PREC);
  }
  for (int s = 0; s < 3; s++) arb_clear(sq[s]);
  arb_clear(A2s); arb_clear(B2); arb_clear(EA); arb_clear(EB); arb_clear(EAB); arb_clear(cr); arb_clear(c0); arb_clear(t); arb_clear(u);
  arb_clear(w); arb_clear(four); arb_clear(one); arb_clear(two); arb_clear(pi); arb_clear(dmn); arb_clear(dmx); arb_clear(term);
  return ret;
}

/* ===== window-3 conn automaton (own implementation of Lemma 1, W3.md Section 2) ===== */
/* state: window (oldest first, size win <= 3), component labels lab[] (canonical), capped degrees cnt[], u (0 or 1) */
#define MAXS 512
static int NSTA = 0; static int Swin[MAXS], Slab[MAXS][3], Scnt[MAXS][3], Su[MAXS];
static int sfind(int win, const int *lab, const int *cnt, int u) {
  for (int q = 0; q < NSTA; q++) {
    if (Swin[q] != win || Su[q] != u) continue;
    int ok = 1; for (int i = 0; i < win; i++) if (Slab[q][i] != lab[i] || Scnt[q][i] != cnt[i]) { ok = 0; break; }
    if (ok) return q;
  }
  if (NSTA >= MAXS) { fprintf(stderr, "automaton: too many states\n"); exit(7); }
  Swin[NSTA] = win; Su[NSTA] = u; for (int i = 0; i < 3; i++) { Slab[NSTA][i] = i < win ? lab[i] : -1; Scnt[NSTA][i] = i < win ? cnt[i] : -1; }
  return NSTA++;
}
static int ufind(int *par, int x) { while (par[x] != x) x = par[x] = par[par[x]]; return x; }
/* add a point with sure edges N (to the newest window point), S (second newest), T (third newest).
   Returns the new state, or -1 if dead. If cl != NULL, also returns the closing value (point added is the last one). */
static int sstep(int s, int N, int S, int T, double *cl) {
  int win = Swin[s], u = Su[s], par[4], cnt[4];
  for (int i = 0; i < win; i++) { cnt[i] = Scnt[s][i]; par[i] = i; }
  for (int i = 0; i < win; i++) for (int j = 0; j < i; j++) if (Slab[s][j] == Slab[s][i]) { par[i] = j; break; }
  int q = win; par[q] = q; cnt[q] = 0;
  int e[3] = {N, S, T};
  for (int d = 1; d <= 3; d++) {
    if (q - d < 0 || !e[d - 1]) continue;
    int a = ufind(par, q), b = ufind(par, q - d); if (a != b) par[a] = b;
    cnt[q]++; cnt[q - d]++;
  }
  for (int i = 0; i <= q; i++) if (cnt[i] > 2) cnt[i] = 2;
  int first = 0, nwin = win + 1;
  if (nwin > 3) {                      /* the oldest point leaves: degree final, component must meet the new window */
    int r0 = ufind(par, 0), meets = 0;
    for (int i = 1; i <= q; i++) if (ufind(par, i) == r0) meets = 1;
    if (!meets) { if (cl) *cl = 0; return -1; }
    if (cnt[0] < 2) u++;
    if (u >= 2) { if (cl) *cl = 0; return -1; }
    first = 1; nwin = 3;
  }
  int lab[3], c2[3], map[4], nl = 0;
  for (int i = 0; i < 4; i++) map[i] = -1;
  for (int i = first; i <= q; i++) { int r = ufind(par, i); if (map[r] < 0) map[r] = nl++; lab[i - first] = map[r]; c2[i - first] = cnt[i]; }
  if (cl) {                            /* closing: window one component; all degrees final */
    if (nl != 1) { *cl = 0; }
    else { int uf = u; for (int i = 0; i < nwin; i++) if (c2[i] < 2) uf++; double v = 1.0 - 0.5 * uf; *cl = v > 0 ? v : 0; }
  }
  return sfind(nwin, lab, c2, u);
}
static int TRN[MAXS][2][2][2]; static double CLV[MAXS][2][2][2];
static void build_auto(void) {
  int lab0[3] = {0, 0, 0}, cnt0[3] = {0, 0, 0};
  sfind(1, lab0, cnt0, 0);            /* state 0: just y_0 */
  for (int q = 0; q < NSTA; q++)      /* closure (NSTA grows) */
    for (int N = 0; N < 2; N++) for (int S = 0; S < 2; S++) for (int T = 0; T < 2; T++) {
      double c; int t = sstep(q, N, S, T, &c);
      TRN[q][N][S][T] = t; CLV[q][N][S][T] = c;
    }
  fprintf(stderr, "automaton (window-3 conn, own): %d states\n", NSTA);
}
/* ===== grid, per-ring data, pair and triple tables ===== */
static int N1, N2, NR, NT, ND, NC, KMAX, NTH;
static arb_ptr RBA;                  /* radii (arb, exact rationals) */
static double *RBD;                  /* radii (double, nearest) */
static double DTH;                   /* pi/NT (double) */
static arb_t DTHA;                   /* pi/NT (arb) */
static double *AREA_LO, *AREA_HI;    /* cell areas: lower / upper doubles */
static arb_ptr RHOC, MOM;            /* centroid radius and second moment about the centroid, per ring */
static double *UUP;                  /* E u(|z|) over the cell: upper bound (double, rounded up) */
static arb_ptr ULO;                  /* E u(|z|): lower bound (exact arb) */
static double *HMIN;                 /* min |z| over the hull: r1 cos(dth/2), rounded down */
#define EPSW 1e-12                   /* widening of distance ranges (rounded centres; cell rounding) */
static double upd(const arb_t x) { arf_t u; arf_init(u); arb_get_ubound_arf(u, x, PREC); double d = arf_get_d(u, ARF_RND_UP); arf_clear(u); return d; }
static double lod(const arb_t x) { arf_t u; arf_init(u); arb_get_lbound_arf(u, x, PREC); double d = arf_get_d(u, ARF_RND_DOWN); arf_clear(u); return d; }
static void setlo(arb_t x) { arf_t u; arf_init(u); arb_get_lbound_arf(u, x, PREC); arb_set_arf(x, u); arf_clear(u); }
static PC mkcell(int ir, int itrel) {  /* cell of ring ir at angles [itrel dth, (itrel+1) dth] (reference frame) */
  PC c; c.r1 = RBD[ir]; c.r2 = RBD[ir + 1]; c.t1 = itrel * DTH; c.t2 = (itrel + 1) * DTH; return c;
}
/* centroid of ring ir at the reference angle slot itrel: arb coordinates */
static void centroid(arb_t cx, arb_t cy, int ir, int itrel) {
  arb_t a; arb_init(a);
  arb_mul_si(a, DTHA, 2 * itrel + 1, PREC); arb_mul_2exp_si(a, a, -1);
  arb_sin_cos(cy, cx, a, PREC); arb_mul(cx, cx, RHOC + ir, PREC); arb_mul(cy, cy, RHOC + ir, PREC);
  arb_clear(a);
}
/* round an arb point to doubles; e >= distance between the point and the rounded point */
static void rnd_pt(double *x, double *y, arb_t e, const arb_t px, const arb_t py) {
  *x = arf_get_d(arb_midref(px), ARF_RND_NEAR); *y = arf_get_d(arb_midref(py), ARF_RND_NEAR);
  arb_t dx, dy; arb_init(dx); arb_init(dy);
  arb_set_d(dx, *x); arb_sub(dx, px, dx, PREC); arb_set_d(dy, *y); arb_sub(dy, py, dy, PREC);
  arb_sqr(dx, dx, PREC); arb_sqr(dy, dy, PREC); arb_add(dx, dx, dy, PREC); arb_sqrt(e, dx, PREC);
  { arf_t u; arf_init(u); arb_get_ubound_arf(u, e, PREC); arb_set_arf(e, u); arf_clear(u); }
  arb_clear(dx); arb_clear(dy);
}
static void per_ring(void) {
  AREA_LO = malloc(sizeof(double) * NR); AREA_HI = malloc(sizeof(double) * NR); UUP = malloc(sizeof(double) * NR); HMIN = malloc(sizeof(double) * NR);
  RHOC = _arb_vec_init(NR); MOM = _arb_vec_init(NR); ULO = _arb_vec_init(NR);
  arb_t t, u, v, sinc, half, ch; arb_init(t); arb_init(u); arb_init(v); arb_init(sinc); arb_init(half); arb_init(ch);
  arb_mul_2exp_si(half, DTHA, -1); arb_sin(sinc, half, PREC); arb_div(sinc, sinc, half, PREC); arb_cos(ch, half, PREC);
  for (int ir = 0; ir < NR; ir++) {
    arb_ptr r1 = RBA + ir, r2 = RBA + ir + 1;
    arb_sqr(t, r2, PREC); arb_sqr(u, r1, PREC); arb_sub(t, t, u, PREC); arb_mul(t, t, DTHA, PREC); arb_mul_2exp_si(t, t, -1);
    AREA_LO[ir] = lod(t); AREA_HI[ir] = upd(t);
    arb_pow_ui(t, r2, 3, PREC); arb_pow_ui(u, r1, 3, PREC); arb_sub(t, t, u, PREC);
    arb_sqr(u, r2, PREC); arb_sqr(v, r1, PREC); arb_sub(u, u, v, PREC); arb_div(t, t, u, PREC);
    arb_mul_ui(t, t, 2, PREC); arb_div_ui(t, t, 3, PREC); arb_mul(RHOC + ir, t, sinc, PREC);
    arb_sqr(t, r1, PREC); arb_sqr(u, r2, PREC); arb_add(t, t, u, PREC); arb_mul_2exp_si(t, t, -1);
    arb_sqr(u, RHOC + ir, PREC); arb_sub(MOM + ir, t, u, PREC);
    { arf_t ub; arf_init(ub); arb_get_ubound_arf(ub, MOM + ir, PREC); arb_set_arf(MOM + ir, ub); arf_clear(ub); if (arb_is_negative(MOM + ir)) arb_zero(MOM + ir); }
    arb_mul(t, r1, ch, PREC); HMIN[ir] = lod(t);
    /* E u(|z|): two-sided Lemma V for B(-z) u B(0) (one moving centre, distance |z| in [HMIN, r2]) and monotone fallbacks */
    arb_t cx, cy, e, A2c, Er, ub2, lb2; arb_init(cx); arb_init(cy); arb_init(e); arb_init(A2c); arb_init(Er); arb_init(ub2); arb_init(lb2);
    centroid(cx, cy, ir, 0);
    double x, y; rnd_pt(&x, &y, e, cx, cy);
    arb_set_d(t, hypot(x, y)); arb_set_d(u, x); arb_sqr(u, u, PREC); arb_set_d(v, y); arb_sqr(v, v, PREC); arb_add(u, u, v, PREC); arb_sqrt(t, u, PREC);
    ucres(A2c, t);                                                      /* u(|Ct|) = A2(Ct) - pi */
    int al[2][3] = {{-1, 0, 0}, {0, 0, 0}};
    LVP pr[1] = {{0, 1, HMIN[ir] - EPSW, RBD[ir + 1] + EPSW}};
    arb_ptr ej = _arb_vec_init(2); arb_set(ej + 0, e); arb_zero(ej + 1);
    int ok = lemv_corr(Er, 1, (const int (*)[3])al, MOM + ir, ej, pr, 1);
    arb_set(t, r2); ucres(ub2, t);                                      /* u(max |z|) */
    arb_set_d(t, HMIN[ir] > 0 ? HMIN[ir] : 0); ucres(lb2, t);           /* u(min |z|) */
    if (ok == 0) {
      arb_mul_2exp_si(u, e, 1); arb_add(v, A2c, u, PREC); arb_add(v, v, Er, PREC);   /* u(|Ct|) + 2e + E r */
      UUP[ir] = upd(v) < upd(ub2) ? upd(v) : upd(ub2);
      arb_sub(v, A2c, u, PREC); arb_sub(v, v, Er, PREC); setlo(v); setlo(lb2);
      if (arb_gt(v, lb2)) arb_set(ULO + ir, v); else arb_set(ULO + ir, lb2);
    } else { UUP[ir] = upd(ub2); setlo(lb2); arb_set(ULO + ir, lb2); }
    _arb_vec_clear(ej, 2);
    arb_clear(cx); arb_clear(cy); arb_clear(e); arb_clear(A2c); arb_clear(Er); arb_clear(ub2); arb_clear(lb2);
    if (!isfinite(AREA_LO[ir]) || !isfinite(UUP[ir]) || !arb_is_finite(ULO + ir) || !arb_is_finite(MOM + ir)) { fprintf(stderr, "NaN in ring data %d\n", ir); exit(13); }
  }
  arb_clear(t); arb_clear(u); arb_clear(v); arb_clear(sinc); arb_clear(half); arb_clear(ch);
}

/* pair tables over (ia, ib, d), d = it_b - it_a: S class, abar2 (upper, double), LV3LO (lower, double) */
static signed char *SCL; static double *AB2, *LV3;
static size_t pidx(int ia, int ib, int d) { return ((size_t)ia * NR + ib) * ND + (d + NT - 1); }
static long long n_lvfail2 = 0, n_unfail2 = 0;
static void pair_entry(int ia, int ib, int d) {
  size_t id = pidx(ia, ib, d);
  PC ca = mkcell(ia, 0), cb = mkcell(ib, d), cab[2] = {ca, cb};
  double smin, smax; hrange(cab, 2, &smin, &smax);
  SCL[id] = (smax <= 1.0) ? 1 : 0;
  arb_t ax, ay, bx, by, e0, e2, ePa, ePb, A, Er, t, u, v; arb_init(ax); arb_init(ay); arb_init(bx); arb_init(by); arb_init(e0); arb_init(e2);
  arb_init(ePa); arb_init(ePb); arb_init(A); arb_init(Er); arb_init(t); arb_init(u); arb_init(v);
  arb_ptr X = _arb_vec_init(4), Y = _arb_vec_init(4), mom = _arb_vec_init(3), ej = _arb_vec_init(4);
  centroid(ax, ay, ia, 0); centroid(bx, by, ib, d);
  arb_set(mom + 0, MOM + ia); arb_set(mom + 1, MOM + ib); arb_zero(mom + 2);
  /* ---- abar2: centres Q0 = -z_a, Q1 = 0, Q2 = z_b ---- */
  double x0, y0, x2, y2;
  arb_neg(t, ax); arb_neg(u, ay); rnd_pt(&x0, &y0, e0, t, u);
  rnd_pt(&x2, &y2, e2, bx, by);
  double fb = UUP[ib], best = fb;
  arb_set_d(X + 0, x0); arb_set_d(Y + 0, y0); arb_zero(X + 1); arb_zero(Y + 1); arb_set_d(X + 2, x2); arb_set_d(Y + 2, y2);
  if (union_n(3, A, X, Y) == 0) {
    int al[3][3] = {{-1, 0, 0}, {0, 0, 0}, {0, 1, 0}};
    LVP pr[3] = {{0, 1, HMIN[ia] - EPSW, RBD[ia + 1] + EPSW}, {0, 2, smin - EPSW, smax + EPSW}, {1, 2, HMIN[ib] - EPSW, RBD[ib + 1] + EPSW}};
    arb_set(ej + 0, e0); arb_zero(ej + 1); arb_set(ej + 2, e2);
    if (lemv_corr(Er, 2, (const int (*)[3])al, mom, ej, pr, 3) == 0) {
      arb_add(t, e0, e2, PREC); arb_mul_2exp_si(t, t, 1);               /* linear term <= 2 sum e_j */
      arb_add(t, t, A, PREC); arb_add(t, t, Er, PREC);
      arb_sub(t, t, ULO + ia, PREC); arb_const_pi(u, PREC); arb_sub(t, t, u, PREC);   /* - E[A2'] lower = - (pi + E u(|z_a|)_lo) */
      double lv = upd(t); if (lv < best) best = lv;
    } else { n_lvfail2++; }
  } else { n_unfail2++; }
  if (!(best >= 0) || !isfinite(best)) { fprintf(stderr, "invalid abar2 %g at (%d,%d,%d)\n", best, ia, ib, d); exit(5); }
  AB2[id] = best;
  /* ---- LV3LO: E[A3] lower, A3 = |B(P0) u B(P1) u B(P2)|, P0 = -(z_a + z_b), P1 = -z_b, P2 = 0 ---- */
  double p0x, p0y, p1x, p1y;
  arb_add(t, ax, bx, PREC); arb_neg(t, t); arb_add(u, ay, by, PREC); arb_neg(u, u); rnd_pt(&p0x, &p0y, ePa, t, u);
  arb_neg(t, bx); arb_neg(u, by); rnd_pt(&p1x, &p1y, ePb, t, u);
  arb_t lo, cand; arb_init(lo); arb_init(cand);
  arb_const_pi(lo, PREC); arb_add(lo, lo, ULO + ib, PREC);                          /* B(P1) u B(P2): pi + E u(|z_b|) */
  arb_const_pi(cand, PREC); arb_add(cand, cand, ULO + ia, PREC); arb_max(lo, lo, cand, PREC);   /* B(P0) u B(P1): |P1-P0| = |z_a| */
  arb_set_d(t, smin); ucres(cand, t); arb_const_pi(u, PREC); arb_add(cand, cand, u, PREC); setlo(cand); arb_max(lo, lo, cand, PREC); /* B(P0) u B(P2) */
  arb_set_d(X + 0, p0x); arb_set_d(Y + 0, p0y); arb_set_d(X + 1, p1x); arb_set_d(Y + 1, p1y); arb_zero(X + 2); arb_zero(Y + 2);
  if (union_n(3, A, X, Y) == 0) {
    int al[3][3] = {{-1, -1, 0}, {0, -1, 0}, {0, 0, 0}};
    LVP pr[3] = {{0, 1, HMIN[ia] - EPSW, RBD[ia + 1] + EPSW}, {0, 2, smin - EPSW, smax + EPSW}, {1, 2, HMIN[ib] - EPSW, RBD[ib + 1] + EPSW}};
    arb_set(ej + 0, ePa); arb_set(ej + 1, ePb); arb_zero(ej + 2);
    if (lemv_corr(Er, 2, (const int (*)[3])al, mom, ej, pr, 3) == 0) {
      arb_add(t, ePa, ePb, PREC); arb_mul_2exp_si(t, t, 1);
      arb_sub(cand, A, t, PREC); arb_sub(cand, cand, Er, PREC); setlo(cand);
      arb_max(lo, lo, cand, PREC);
    }
  }
  LV3[id] = lod(lo);
  if (!isfinite(LV3[id])) { fprintf(stderr, "invalid LV3LO at (%d,%d,%d)\n", ia, ib, d); exit(5); }
  arb_clear(lo); arb_clear(cand);
  _arb_vec_clear(X, 4); _arb_vec_clear(Y, 4); _arb_vec_clear(mom, 3); _arb_vec_clear(ej, 4);
  arb_clear(ax); arb_clear(ay); arb_clear(bx); arb_clear(by); arb_clear(e0); arb_clear(e2); arb_clear(ePa); arb_clear(ePb);
  arb_clear(A); arb_clear(Er); arb_clear(t); arb_clear(u); arb_clear(v);
}
static void float_pair(int ia, int ib, int d);
static int FLOATNS;
static void pair_tables(void) {
  size_t PS = (size_t)NR * NR * ND;
  SCL = malloc(PS); AB2 = malloc(sizeof(double) * PS); LV3 = malloc(sizeof(double) * PS);
  #pragma omp parallel for schedule(dynamic, 1)
  for (int pp = 0; pp < NR * NR; pp++) for (int d = -(NT - 1); d <= NT - 1; d++) { if (FLOATNS) float_pair(pp / NR, pp % NR, d); else pair_entry(pp / NR, pp % NR, d); }
  fprintf(stderr, "pair tables: %zu entries (Lemma V fallback %lld, union undecided %lld)\n", PS, n_lvfail2, n_unfail2);
}

/* triple tables over (ia, ib, ic, dab, dbc): T class (byte; 2 = unrealizable) and abar3 (float, rounded up) */
static float *AB3; static signed char *TCL;
static size_t TS3;
static size_t tidx(int ia, int ib, int ic, int dab, int dbc) { return ((((size_t)ia * NR + ib) * NR + ic) * ND + (dab + NT - 1)) * ND + (dbc + NT - 1); }
static long long n_far = 0, n_lvfail3 = 0, n_unfail3 = 0, n_t1 = 0;
static double minab3 = 1e300;
static void triple_block(int ia, int ib, int ic) {
  arb_t ax, ay, bx, by, cx, cy, t, u, A, Er, ePa, ePb, ePc, up;
  arb_init(ax); arb_init(ay); arb_init(bx); arb_init(by); arb_init(cx); arb_init(cy); arb_init(t); arb_init(u); arb_init(A); arb_init(Er);
  arb_init(ePa); arb_init(ePb); arb_init(ePc); arb_init(up);
  arb_ptr X = _arb_vec_init(4), Y = _arb_vec_init(4), mom = _arb_vec_init(3), ej = _arb_vec_init(4);
  arb_set(mom + 0, MOM + ia); arb_set(mom + 1, MOM + ib); arb_set(mom + 2, MOM + ic);
  long long lfar = 0, llv = 0, lun = 0, lt1 = 0; double lmin = 1e300;
  centroid(ax, ay, ia, 0);
  for (int dab = -(NT - 1); dab <= NT - 1; dab++) for (int dbc = -(NT - 1); dbc <= NT - 1; dbc++) {
    size_t id = tidx(ia, ib, ic, dab, dbc);
    if (abs(dab + dbc) > NT - 1) { TCL[id] = 2; AB3[id] = 0; continue; }     /* unrealizable: never used */
    PC ca = mkcell(ia, 0), cb = mkcell(ib, dab), cc = mkcell(ic, dab + dbc);
    PC c3[3] = {ca, cb, cc}, cab[2] = {ca, cb}, cbc[2] = {cb, cc};
    double m3, M3, mab, Mab, mbc, Mbc;
    hrange(c3, 3, &m3, &M3); hrange(cab, 2, &mab, &Mab); hrange(cbc, 2, &mbc, &Mbc);
    TCL[id] = (M3 <= 1.0) ? 1 : 0; if (TCL[id]) lt1++;
    double a2 = AB2[pidx(ib, ic, dbc)], best = a2;
    if (m3 - EPSW >= 2.0) { lfar++; }                                         /* far: v3 = v2(z_b, z_c) a.e. */
    else {
      centroid(bx, by, ib, dab); centroid(cx, cy, ic, dab + dbc);
      double p0x, p0y, p1x, p1y, p3x, p3y;
      arb_add(t, ax, bx, PREC); arb_neg(t, t); arb_add(u, ay, by, PREC); arb_neg(u, u); rnd_pt(&p0x, &p0y, ePa, t, u);
      arb_neg(t, bx); arb_neg(u, by); rnd_pt(&p1x, &p1y, ePb, t, u);
      rnd_pt(&p3x, &p3y, ePc, cx, cy);
      arb_set_d(X + 0, p0x); arb_set_d(Y + 0, p0y); arb_set_d(X + 1, p1x); arb_set_d(Y + 1, p1y);
      arb_zero(X + 2); arb_zero(Y + 2); arb_set_d(X + 3, p3x); arb_set_d(Y + 3, p3y);
      if (union_n(4, A, X, Y) == 0) {
        int al[4][3] = {{-1, -1, 0}, {0, -1, 0}, {0, 0, 0}, {0, 0, 1}};
        LVP pr[6] = {{0, 1, HMIN[ia] - EPSW, RBD[ia + 1] + EPSW}, {0, 2, mab - EPSW, Mab + EPSW}, {0, 3, m3 - EPSW, M3 + EPSW},
                     {1, 2, HMIN[ib] - EPSW, RBD[ib + 1] + EPSW}, {1, 3, mbc - EPSW, Mbc + EPSW}, {2, 3, HMIN[ic] - EPSW, RBD[ic + 1] + EPSW}};
        arb_set(ej + 0, ePa); arb_set(ej + 1, ePb); arb_zero(ej + 2); arb_set(ej + 3, ePc);
        if (lemv_corr(Er, 3, (const int (*)[3])al, mom, ej, pr, 6) == 0) {
          arb_add(t, ePa, ePb, PREC); arb_add(t, t, ePc, PREC); arb_mul_2exp_si(t, t, 1);
          arb_add(up, A, t, PREC); arb_add(up, up, Er, PREC);                 /* E[A4] upper */
          arb_set_d(t, LV3[pidx(ia, ib, dab)]); arb_sub(up, up, t, PREC);      /* - E[A3] lower */
          double cand = upd(up);
          if (!(cand >= 0)) { fprintf(stderr, "negative or invalid abar3 candidate %g at (%d,%d,%d,%d,%d): abort\n", cand, ia, ib, ic, dab, dbc); exit(5); }
          if (cand < best) best = cand;
        } else llv++;
      } else lun++;
    }
    float bf = (float)best; if ((double)bf < best) bf = nextafterf(bf, INFINITY);
    AB3[id] = bf; if (best < lmin) lmin = best;
  }
  #pragma omp atomic
  n_far += lfar;
  #pragma omp atomic
  n_lvfail3 += llv;
  #pragma omp atomic
  n_unfail3 += lun;
  #pragma omp atomic
  n_t1 += lt1;
  #pragma omp critical
  { if (lmin < minab3) minab3 = lmin; }
  _arb_vec_clear(X, 4); _arb_vec_clear(Y, 4); _arb_vec_clear(mom, 3); _arb_vec_clear(ej, 4);
  arb_clear(ax); arb_clear(ay); arb_clear(bx); arb_clear(by); arb_clear(cx); arb_clear(cy); arb_clear(t); arb_clear(u); arb_clear(A); arb_clear(Er);
  arb_clear(ePa); arb_clear(ePb); arb_clear(ePc); arb_clear(up);
}
/* ===== recursion with directed rounding ===== */
/* GEMM: C (m x n) = A (m x k, row-major) * Bt^T (Bt: n x k row-major). OpenBLAS (single-threaded, called from OpenMP threads,
   so it runs in the calling thread with its rounding mode) or a plain loop; both round every operation in the current mode. */
#ifdef USE_OPENBLAS
#include <cblas.h>
extern void openblas_set_num_threads(int);
static void GEMM_NT(int m, int n, int k, const double *A, int lda, const double *Bt, int ldb, double *C, int ldc) {
  cblas_dgemm(CblasRowMajor, CblasNoTrans, CblasTrans, m, n, k, 1.0, A, lda, Bt, ldb, 0.0, C, ldc);
}
#else
static void openblas_set_num_threads(int n) { (void)n; }
static void GEMM_NT(int m, int n, int k, const double *A, int lda, const double *Bt, int ldb, double *C, int ldc) {
  for (int i = 0; i < m; i++) for (int j = 0; j < n; j++) {
    const double *a = A + (size_t)i * lda, *b = Bt + (size_t)j * ldb; double sum = 0;
    for (int l = 0; l < k; l++) sum += a[l] * b[l];
    C[(size_t)i * ldc + j] = sum; }
}
#endif

static double *KT2; static float *KT3; static signed char *TCLT;
static size_t kidx(int ia, int ib, int ic, int dab, int dbc) { return (((size_t)ib * NR + ic) * ND + (dbc + NT - 1)) * ((size_t)NR * ND) + (size_t)ia * ND + (dab + NT - 1); }
static void build_tclt(void) {
  TCLT = malloc(TS3); if (!TCLT) { fprintf(stderr, "no memory for TCLT\n"); exit(9); }
  #pragma omp parallel for schedule(static)
  for (long long b = 0; b < (long long)NR * NR * NR; b++) { int ia = (int)(b / (NR * NR)), ib = (int)((b / NR) % NR), ic = (int)(b % NR);
    for (int dab = -(NT - 1); dab <= NT - 1; dab++) for (int dbc = -(NT - 1); dbc <= NT - 1; dbc++) TCLT[kidx(ia, ib, ic, dab, dbc)] = TCL[tidx(ia, ib, ic, dab, dbc)]; }
}
static const double FACD = 1.0 - 0x1p-40, FACU = 1.0 + 0x1p-40;
static int NFL(int c) { int ir = c / NT; return ir + 1 <= N1; }   /* N class: r2 <= 1 (1 is a grid radius) */
static void kernels(double t, int pass) {
  int mode = pass ? FE_UPWARD : FE_DOWNWARD; double fac = pass ? FACU : FACD; double mt = -t;
  size_t PS = (size_t)NR * NR * ND;
  #pragma omp parallel
  {
    fesetround(mode);
    if (!rounding_selftest(mode)) { fprintf(stderr, "thread rounding failure\n"); exit(11); }
    #pragma omp for schedule(dynamic, 1)
    for (long long b = 0; b < (long long)NR * NR * NR; b++) {      /* source block (ia, ib, ic) in AB3 layout -> transposed KT3 */
      int ia = (int)(b / (NR * NR)), ib = (int)((b / NR) % NR), ic = (int)(b % NR);
      double ar = pass ? AREA_HI[ic] : AREA_LO[ic];
      double buf[1024]; int dabv[1024], dbcv[1024];
      for (int dab = -(NT - 1); dab <= NT - 1; dab++) {
        int n = 0;
        for (int dbc = -(NT - 1); dbc <= NT - 1; dbc++) { size_t id = tidx(ia, ib, ic, dab, dbc);
          if (TCL[id] == 2) { KT3[kidx(ia, ib, ic, dab, dbc)] = 0.0f; continue; }
          buf[n] = mt * (double)AB3[id]; dabv[n] = dab; dbcv[n] = dbc; n++; }      /* argument rounded in the mode */
        fesetround(FE_TONEAREST);
        for (int q = 0; q < n; q++) buf[q] = exp(buf[q]);
        fesetround(mode);
        for (int q = 0; q < n; q++) KT3[kidx(ia, ib, ic, dabv[q], dbcv[q])] = (float)((buf[q] * fac) * ar);   /* rounds in the mode */
      }
    }
    #pragma omp for schedule(static)
    for (size_t q = 0; q < PS; q++) {
      int ib = (int)((q / ND) % NR); double ar = pass ? AREA_HI[ib] : AREA_LO[ib];
      double a = mt * AB2[q]; fesetround(FE_TONEAREST); double e = exp(a); fesetround(mode);
      KT2[q] = (e * fac) * ar;
    }
  }
}

static void par_zero(double *x, size_t n) {
  #pragma omp parallel for schedule(static)
  for (size_t c = 0; c < n; c += 1 << 20) { size_t e = c + (1 << 20) < n ? c + (1 << 20) : n; memset(x + c, 0, sizeof(double) * (e - c)); }
}
static double par_max(const double *x, size_t n) {
  double mx = 0;
  #pragma omp parallel for schedule(static) reduction(max:mx)
  for (size_t q = 0; q < n; q++) if (x[q] > mx) mx = x[q];
  return mx;
}
static void par_scale2(double *x, size_t n, int e, int mode) {   /* x *= 2^-e (exact; subnormal results round in the mode) */
  #pragma omp parallel
  { fesetround(mode);
    #pragma omp for schedule(static)
    for (size_t q = 0; q < n; q++) x[q] = ldexp(x[q], -e); }
}
/* returns via phm/phe (mantissa, exponent) the closing sums for k = 3..KMAX at t, pass */
static void recursion(double t, int pass, double *phm, int *phe) {
  int mode = pass ? FE_UPWARD : FE_DOWNWARD; double fac = pass ? FACU : FACD;
  kernels(t, pass);
  fesetround(mode);
  size_t FS = (size_t)NC * NC * NSTA;
  static double *F = NULL, *G = NULL, *clc = NULL;
  if (!F) { F = malloc(sizeof(double) * FS); G = malloc(sizeof(double) * FS); clc = malloc(sizeof(double) * NC);
            if (!F || !G || !clc) { fprintf(stderr, "no memory for the recursion\n"); exit(9); } }
  for (int k = 0; k <= KMAX; k++) { phm[k] = 0; phe[k] = 0; }
  /* level-1 factors |Z_1| e^{-t ubar(Z_1)} with directed rounding */
  double L1[1024];
  for (int ir = 0; ir < NR; ir++) {
    fesetround(mode); double a = (-t) * UUP[ir];
    fesetround(FE_TONEAREST); double e = exp(a);
    fesetround(mode); L1[ir] = (e * fac) * (pass ? AREA_HI[ir] : AREA_LO[ir]);
  }
  /* level 1 and 2 */
  par_zero(G, FS);
  double cl3 = 0;
  #pragma omp parallel
  {
    fesetround(mode);
    #pragma omp for schedule(dynamic, 8) reduction(+:cl3)
    for (int c2 = 0; c2 < NC; c2++) {
      int ir2 = c2 / NT, it2 = c2 % NT, N2c = NFL(c2); double acc = 0;
      for (int c1 = 0; c1 < NC; c1++) {
        int ir1 = c1 / NT, it1 = c1 % NT;
        int D0 = TRN[0][NFL(c1)][0][0]; if (D0 < 0) continue;
        double a1 = L1[ir1];
        size_t pq = pidx(ir1, ir2, it2 - it1);
        double x = a1 * KT2[pq]; int S = SCL[pq];
        int D1 = TRN[D0][N2c][S][0];
        if (D1 >= 0) G[((size_t)c2 * NC + c1) * NSTA + D1] += x;
        double cv = CLV[D0][N2c][S][0]; if (cv > 0) acc += x * cv;
      }
      cl3 += acc;
    }
  }
  fesetround(mode);
  int E = 0;
  if (KMAX >= 3) { phm[3] = cl3; phe[3] = 0; }
  { double mx = par_max(G, FS);
    if (mx > 0) { int e = ilogb(mx); par_scale2(G, FS, e, mode); E += e; } }
  double *tp = F; F = G; G = tp;
  /* levels i -> i+1 for i >= 2 (closing gives k = i + 2) */
  for (int i = 2; i + 2 <= KMAX; i++) {
    /* GEMM per current cell cb: S_T(D, cc) = sum_ca F[cb][ca][D] K3(ca, cb, cc) 1{T(ca, cb, cc) = T}, T = 0, 1 */
    par_zero(G, FS);
    #pragma omp parallel
    {
      fesetround(mode);
      const int CB = 256;
      double *M = malloc(sizeof(double) * (size_t)NSTA * NC), *K0 = malloc(sizeof(double) * (size_t)NC * CB), *K1 = malloc(sizeof(double) * (size_t)NC * CB);
      double *S0 = malloc(sizeof(double) * (size_t)NSTA * CB), *S1 = malloc(sizeof(double) * (size_t)NSTA * CB);
      if (!M || !K0 || !K1 || !S0 || !S1) { fprintf(stderr, "no memory (thread buffers)\n"); exit(9); }
      int Dl[MAXS]; char act[MAXS]; int *cal = malloc(sizeof(int) * NC);
      #pragma omp for schedule(dynamic, 1)
      for (int cb = 0; cb < NC; cb++) {
        const double *Fb = F + (size_t)cb * NC * NSTA;
        int na = 0, kc = 0;
        for (int D = 0; D < NSTA; D++) act[D] = 0;
        for (int ca = 0; ca < NC; ca++) { const double *f = Fb + (size_t)ca * NSTA; int any = 0;
          for (int D = 0; D < NSTA; D++) if (f[D] > 0) { any = 1; act[D] = 1; }
          if (any) cal[kc++] = ca; }
        for (int D = 0; D < NSTA; D++) if (act[D]) Dl[na++] = D;
        if (!na) { clc[cb] = 0; continue; }
        for (int r = 0; r < na; r++) { double *mr = M + (size_t)r * kc; int D = Dl[r]; for (int q = 0; q < kc; q++) mr[q] = Fb[(size_t)cal[q] * NSTA + D]; }
        int ib = cb / NT, itb = cb % NT; double acc = 0;
        for (int c0 = 0; c0 < NC; c0 += CB) {
          int nb = (c0 + CB <= NC) ? CB : NC - c0;
          for (int j = 0; j < nb; j++) {                                   /* K_T^T rows: one per target cell cc */
            int cc = c0 + j, ic = cc / NT, itc = cc % NT;
            size_t blk = kidx(0, ib, ic, 0, itc - itb) - (NT - 1);
            double *k0 = K0 + (size_t)j * kc, *k1 = K1 + (size_t)j * kc;
            for (int q = 0; q < kc; q++) {
              int ca = cal[q], ia = ca / NT, ita = ca % NT; size_t id = blk + (size_t)ia * ND + (itb - ita + NT - 1);
              double K = (double)KT3[id]; int T = TCLT[id];
              k0[q] = T ? 0.0 : K; k1[q] = T ? K : 0.0;
            }
          }
          GEMM_NT(na, nb, kc, M, kc, K0, kc, S0, nb);
          GEMM_NT(na, nb, kc, M, kc, K1, kc, S1, nb);
          for (int j = 0; j < nb; j++) {
            int cc = c0 + j, ic = cc / NT, itc = cc % NT, Nc = NFL(cc), S = SCL[pidx(ib, ic, itc - itb)];
            double *g = G + ((size_t)cc * NC + cb) * NSTA;
            for (int r = 0; r < na; r++) {
              int D = Dl[r]; double s0 = S0[(size_t)r * nb + j], s1 = S1[(size_t)r * nb + j];
              if (s0 > 0) { int D2 = TRN[D][Nc][S][0]; if (D2 >= 0) g[D2] += s0; double cv = CLV[D][Nc][S][0]; if (cv > 0) acc += s0 * cv; }
              if (s1 > 0) { int D2 = TRN[D][Nc][S][1]; if (D2 >= 0) g[D2] += s1; double cv = CLV[D][Nc][S][1]; if (cv > 0) acc += s1 * cv; }
            }
          }
        }
        clc[cb] = acc;
      }
      free(M); free(K0); free(K1); free(S0); free(S1); free(cal);
    }
    fesetround(mode);
    double cs = 0; for (int cc = 0; cc < NC; cc++) cs += clc[cc];
    if (!isfinite(cs)) { fprintf(stderr, "non-finite closing sum\n"); exit(14); }
    phm[i + 2] = cs; phe[i + 2] = E;
    double mx = par_max(G, FS);
    if (!(mx > 0)) break;
    int e = ilogb(mx); par_scale2(G, FS, e, mode); E += e;
    tp = F; F = G; G = tp;
  }
  fesetround(FE_TONEAREST);
}
/* ===== FLOAT validation mode (env CHK3FLOAT=NS): sampled cell averages and majority classes. NOT rigorous. ===== */
static double uarea_f(int n, const double *x, const double *y) {
  double total = 0;
  for (int i = 0; i < n; i++) {
    double lo[8], hi[8]; int m = 0, covered = 0;
    for (int j = 0; j < n; j++) { if (j == i) continue;
      double dx = x[j] - x[i], dy = y[j] - y[i], d = sqrt(dx * dx + dy * dy);
      if (d >= 2) continue;
      if (d == 0) { if (j < i) { covered = 1; break; } else continue; }
      double ph = atan2(dy, dx), a = acos(d / 2); lo[m] = ph - a; hi[m] = ph + a; m++; }
    if (covered) continue;
    double L[16], H[16]; int q = 0;
    for (int t = 0; t < m; t++) { double a0 = lo[t], b0 = hi[t];
      while (a0 < 0) { a0 += 2 * M_PI; b0 += 2 * M_PI; } while (a0 >= 2 * M_PI) { a0 -= 2 * M_PI; b0 -= 2 * M_PI; }
      if (b0 <= 2 * M_PI) { L[q] = a0; H[q] = b0; q++; } else { L[q] = a0; H[q] = 2 * M_PI; q++; L[q] = 0; H[q] = b0 - 2 * M_PI; q++; } }
    for (int s2 = 1; s2 < q; s2++) { double a0 = L[s2], b0 = H[s2]; int r = s2 - 1;
      while (r >= 0 && L[r] > a0) { L[r + 1] = L[r]; H[r + 1] = H[r]; r--; } L[r + 1] = a0; H[r + 1] = b0; }
    double cur = 0;
    for (int s2 = 0; s2 <= q; s2++) { double a0 = (s2 < q) ? L[s2] : 2 * M_PI;
      if (a0 > cur) { double t1 = cur, t2 = a0; total += 0.5 * ((t2 - t1) + x[i] * (sin(t2) - sin(t1)) - y[i] * (cos(t2) - cos(t1))); }
      if (s2 < q && H[s2] > cur) cur = H[s2]; }
  }
  return total;
}
static void samp(int ir, int itrel, int i, int j, double *x, double *y) {   /* sample (i, j) of NS x NS in the cell */
  double r1 = RBD[ir], r2 = RBD[ir + 1], r = sqrt(r1 * r1 + (i + 0.5) / FLOATNS * (r2 * r2 - r1 * r1));
  double th = (itrel + (j + 0.5) / FLOATNS) * DTH; *x = r * cos(th); *y = r * sin(th);
}
static void float_ring(int ir) {
  double s = 0; int n = 0;
  for (int i = 0; i < FLOATNS; i++) for (int j = 0; j < FLOATNS; j++) { double x, y; samp(ir, 0, i, j, &x, &y);
    double X[2] = {0, x}, Y[2] = {0, y}; s += uarea_f(2, X, Y) - M_PI; n++; }
  UUP[ir] = s / n; arb_set_d(ULO + ir, s / n);
}
static void float_pair(int ia, int ib, int d) {
  size_t id = pidx(ia, ib, d); int NS = FLOATNS; double s = 0, s3 = 0; int n = 0, ok = 0;
  for (int i = 0; i < NS; i++) for (int j = 0; j < NS; j++) for (int k = 0; k < NS; k++) for (int l = 0; l < NS; l++) {
    double ax, ay, bx, by; samp(ia, 0, i, j, &ax, &ay); samp(ib, d, k, l, &bx, &by);
    double X[3] = {-ax, 0, bx}, Y[3] = {-ay, 0, by};
    s += uarea_f(3, X, Y) - uarea_f(2, X, Y);
    double X3[3] = {-(ax + bx), -bx, 0}, Y3[3] = {-(ay + by), -by, 0}; s3 += uarea_f(3, X3, Y3);
    if ((ax + bx) * (ax + bx) + (ay + by) * (ay + by) <= 1.0) ok++; n++; }
  AB2[id] = s / n; LV3[id] = s3 / n; SCL[id] = (2 * ok >= n) ? 1 : 0;
}
static void float_triple_block(int ia, int ib, int ic) {
  int NS = FLOATNS;
  for (int dab = -(NT - 1); dab <= NT - 1; dab++) for (int dbc = -(NT - 1); dbc <= NT - 1; dbc++) {
    size_t id = tidx(ia, ib, ic, dab, dbc);
    if (abs(dab + dbc) > NT - 1) { TCL[id] = 2; AB3[id] = 0; continue; }
    double s = 0; int n = 0, ok = 0;
    for (int i = 0; i < NS; i++) for (int j = 0; j < NS; j++) for (int k = 0; k < NS; k++) for (int l = 0; l < NS; l++) for (int m = 0; m < NS; m++) for (int o = 0; o < NS; o++) {
      double ax, ay, bx, by, cx, cy; samp(ia, 0, i, j, &ax, &ay); samp(ib, dab, k, l, &bx, &by); samp(ic, dab + dbc, m, o, &cx, &cy);
      double X[4] = {-(ax + bx), -bx, 0, cx}, Y[4] = {-(ay + by), -by, 0, cy};
      s += uarea_f(4, X, Y) - uarea_f(3, X, Y);
      double sx = ax + bx + cx, sy = ay + by + cy; if (sx * sx + sy * sy <= 1.0) ok++; n++; }
    AB3[id] = (float)(s / n); TCL[id] = (2 * ok >= n) ? 1 : 0;
  }
}
/* ===== table self-test (env CHK3TEST="nentries nsamples"): Monte Carlo check of every bound and class on random entries ===== */
static unsigned long long trs = 88172645463325252ULL;
static double tu01(void) { trs ^= trs << 13; trs ^= trs >> 7; trs ^= trs << 17; return (trs >> 11) * 0x1.0p-53; }
static void tsamp(int ir, int itrel, double *x, double *y) {          /* uniform (area) sample in the cell */
  double r1 = RBD[ir], r2 = RBD[ir + 1], r = sqrt(r1 * r1 + tu01() * (r2 * r2 - r1 * r1)), th = (itrel + tu01()) * DTH;
  *x = r * cos(th); *y = r * sin(th);
}
static void tbound(int ir, int itrel, double *x, double *y) {         /* sample on the cell boundary (for the classes) */
  double r1 = RBD[ir], r2 = RBD[ir + 1], u = tu01(); int side = (int)(4 * tu01()); double r, th;
  if (side == 0) { r = r1; th = (itrel + u) * DTH; } else if (side == 1) { r = r2; th = (itrel + u) * DTH; }
  else { r = r1 + u * (r2 - r1); th = (itrel + (side == 2 ? 0 : 1)) * DTH; }
  *x = r * cos(th); *y = r * sin(th);
}
static void selftest(long nent, long ns) {
  double worst_ab2 = 1e9, worst_lv3 = -1e9, worst_ab3 = 1e9, worst_uup = 1e9, worst_ulo = -1e9; long bad = 0, nt1 = 0, ns1 = 0, nrng = 0;
  for (int ir = 0; ir < NR; ir++) {                                    /* ring data */
    double s = 0, s2 = 0;
    for (long q = 0; q < ns; q++) { double x, y; tsamp(ir, 0, &x, &y); double X[2] = {0, x}, Y[2] = {0, y}; double v = uarea_f(2, X, Y) - M_PI; s += v; s2 += v * v; }
    double m = s / ns, se = sqrt((s2 / ns - m * m) / ns) + 1e-15;
    double zu = (UUP[ir] - m) / se, zl = (lod(ULO + ir) - m) / se;
    if (zu < worst_uup) worst_uup = zu; if (zl > worst_ulo) worst_ulo = zl;
    if (zu < -5 || zl > 5) { bad++; fprintf(stderr, "ring %d: UUP %g ULO %g mean %g se %g\n", ir, UUP[ir], lod(ULO + ir), m, se); }
  }
  for (long e = 0; e < nent; e++) {
    int ia = (int)(tu01() * NR), ib = (int)(tu01() * NR), d = (int)(tu01() * ND) - (NT - 1);
    size_t id = pidx(ia, ib, d);
    double s = 0, s2 = 0, t = 0, t2 = 0, smn = 1e9, smx = 0; PC ca = mkcell(ia, 0), cb = mkcell(ib, d), cab[2] = {ca, cb}; double hm, hM; hrange(cab, 2, &hm, &hM);
    for (long q = 0; q < ns; q++) {
      double ax, ay, bx, by; tsamp(ia, 0, &ax, &ay); tsamp(ib, d, &bx, &by);
      double X[3] = {-ax, 0, bx}, Y[3] = {-ay, 0, by}; double v = uarea_f(3, X, Y) - uarea_f(2, X, Y); s += v; s2 += v * v;
      double X3[3] = {-(ax + bx), -bx, 0}, Y3[3] = {-(ay + by), -by, 0}; double a3 = uarea_f(3, X3, Y3); t += a3; t2 += a3 * a3;
      double L = hypot(ax + bx, ay + by); if (L < smn) smn = L; if (L > smx) smx = L;
      tbound(ia, 0, &ax, &ay); tbound(ib, d, &bx, &by); L = hypot(ax + bx, ay + by); if (L < smn) smn = L; if (L > smx) smx = L;
    }
    double m = s / ns, se = sqrt(fmax(s2 / ns - m * m, 0) / ns) + 1e-15, mt = t / ns, st = sqrt(fmax(t2 / ns - mt * mt, 0) / ns) + 1e-15;
    double z2 = (AB2[id] - m) / se, z3 = (LV3[id] - mt) / st;
    if (z2 < worst_ab2) worst_ab2 = z2; if (z3 > worst_lv3) worst_lv3 = z3;
    if (z2 < -5 || z3 > 5) { bad++; fprintf(stderr, "pair (%d,%d,%d): AB2 %g mean %g se %g | LV3 %g mean %g se %g\n", ia, ib, d, AB2[id], m, se, LV3[id], mt, st); }
    if (SCL[id] == 1) { ns1++; if (smx > 1 + 1e-12) { bad++; fprintf(stderr, "S=1 violated (%d,%d,%d): %g\n", ia, ib, d, smx); } }
    if (smn < hm - 1e-9 || smx > hM + 1e-9) { nrng++; bad++; fprintf(stderr, "pair range violated (%d,%d,%d): [%g,%g] vs [%g,%g]\n", ia, ib, d, smn, smx, hm, hM); }
    /* triple */
    int ic = (int)(tu01() * NR), dab = d, dbc = (int)(tu01() * ND) - (NT - 1);
    if (abs(dab + dbc) > NT - 1) continue;
    size_t it = tidx(ia, ib, ic, dab, dbc);
    PC c3[3] = {ca, cb, mkcell(ic, dab + dbc)}; double m3, M3; hrange(c3, 3, &m3, &M3);
    double w = 0, w2 = 0, tmn = 1e9, tmx = 0;
    for (long q = 0; q < ns; q++) {
      double ax, ay, bx, by, cx, cy; tsamp(ia, 0, &ax, &ay); tsamp(ib, dab, &bx, &by); tsamp(ic, dab + dbc, &cx, &cy);
      double X[4] = {-(ax + bx), -bx, 0, cx}, Y[4] = {-(ay + by), -by, 0, cy}; double v = uarea_f(4, X, Y) - uarea_f(3, X, Y); w += v; w2 += v * v;
      double L = hypot(ax + bx + cx, ay + by + cy); if (L < tmn) tmn = L; if (L > tmx) tmx = L;
      tbound(ia, 0, &ax, &ay); tbound(ib, dab, &bx, &by); tbound(ic, dab + dbc, &cx, &cy); L = hypot(ax + bx + cx, ay + by + cy); if (L < tmn) tmn = L; if (L > tmx) tmx = L;
    }
    double mw = w / ns, sw = sqrt(fmax(w2 / ns - mw * mw, 0) / ns) + 1e-15, z = ((double)AB3[it] - mw) / sw;
    if (z < worst_ab3) worst_ab3 = z;
    if (z < -5) { bad++; fprintf(stderr, "triple (%d,%d,%d,%d,%d): AB3 %g mean %g se %g\n", ia, ib, ic, dab, dbc, (double)AB3[it], mw, sw); }
    if (TCL[it] == 1) { nt1++; if (tmx > 1 + 1e-12) { bad++; fprintf(stderr, "T=1 violated (%d,%d,%d,%d,%d): %g\n", ia, ib, ic, dab, dbc, tmx); } }
    if (tmn < m3 - 1e-9 || tmx > M3 + 1e-9) { nrng++; bad++; fprintf(stderr, "triple range violated: [%g,%g] vs [%g,%g]\n", tmn, tmx, m3, M3); }
  }
  fprintf(stderr, "SELFTEST: %ld entries x %ld samples: worst z: AB2 %.2f (>= -5), LV3 %.2f (<= 5), AB3 %.2f (>= -5), UUP %.2f, ULO %.2f; "
                  "S=1 tested %ld, T=1 tested %ld, range violations %ld; BAD %ld\n", nent, ns, worst_ab2, worst_lv3, worst_ab3, worst_uup, worst_ulo, ns1, nt1, nrng, bad);
}
/* ===== triple-table slices ===== */
static void save_slice(const char *fn, int s, int n) {
  FILE *f = fopen(fn, "wb"); if (!f) { fprintf(stderr, "cannot write %s\n", fn); exit(15); }
  int hdr[6] = {0x33484b43, N1, N2, NT, s, n}; fwrite(hdr, sizeof(int), 6, f);
  size_t B = (size_t)ND * ND;
  for (long long b = 0; b < (long long)NR * NR * NR; b++) {
    if (b % n != s) continue;
    fwrite(&b, sizeof(long long), 1, f); fwrite(AB3 + b * B, sizeof(float), B, f); fwrite(TCL + b * B, 1, B, f);
  }
  if (fclose(f)) { fprintf(stderr, "write error %s\n", fn); exit(15); }
}
static void load_slices(const char *list) {
  char buf[8192]; strncpy(buf, list, sizeof(buf) - 1); buf[sizeof(buf) - 1] = 0;
  size_t B = (size_t)ND * ND; long long nblk = (long long)NR * NR * NR;
  char *seen = calloc(nblk, 1); int nfiles = 0, nexp = -1;
  for (char *tok = strtok(buf, " "); tok; tok = strtok(NULL, " ")) {
    FILE *f = fopen(tok, "rb"); if (!f) { fprintf(stderr, "cannot read %s\n", tok); exit(15); }
    int hdr[6]; if (fread(hdr, sizeof(int), 6, f) != 6 || hdr[0] != 0x33484b43 || hdr[1] != N1 || hdr[2] != N2 || hdr[3] != NT) { fprintf(stderr, "bad slice header %s\n", tok); exit(15); }
    if (nexp < 0) nexp = hdr[5]; else if (nexp != hdr[5]) { fprintf(stderr, "slice count mismatch\n"); exit(15); }
    long long b;
    while (fread(&b, sizeof(long long), 1, f) == 1) {
      if (b < 0 || b >= nblk || seen[b] || b % hdr[5] != hdr[4]) { fprintf(stderr, "bad block %lld in %s\n", b, tok); exit(15); }
      if (fread(AB3 + b * B, sizeof(float), B, f) != B || fread(TCL + b * B, 1, B, f) != B) { fprintf(stderr, "short slice %s\n", tok); exit(15); }
      seen[b] = 1;
    }
    fclose(f); nfiles++;
    if (getenv("CHK3LOAD_UNLINK")) unlink(tok);
  }
  for (long long b = 0; b < nblk; b++) if (!seen[b]) { fprintf(stderr, "missing block %lld\n", b); exit(15); }
  free(seen);
  fprintf(stderr, "loaded %d slice files (all %lld blocks)\n", nfiles, nblk);
}

/* ===== t-integral (double, directed rounding; extended secants + GM rule on the log-concave integrand) ===== */
static void tintegral(int DTL, int TT, double **pm, int **pe) {
  int NTV = TT << DTL;
  fesetround(FE_DOWNWARD);
  double sum6 = 0;
  const double PI_HI = nextafter(3.141592653589793, 4.0);
  for (int k = 3; k <= KMAX; k++) {
    double sm1 = k - 1.5;
    double *llo = malloc(sizeof(double) * (NTV + 2)), *lhi = malloc(sizeof(double) * (NTV + 2)); int ok = 1;
    for (int j = 1; j <= NTV; j++) {
      double mD = pm[0][(size_t)k * (NTV + 1) + j], mU = pm[1][(size_t)k * (NTV + 1) + j];
      if (!(mD > 0) || !(mU > 0)) { ok = 0; break; }
      fesetround(FE_DOWNWARD); llo[j] = log_lo(mD) + elog2_lo(pe[0][(size_t)k * (NTV + 1) + j]);
      fesetround(FE_UPWARD); lhi[j] = log_hi(mU) + elog2_hi(pe[1][(size_t)k * (NTV + 1) + j]);
      fesetround(FE_DOWNWARD);
      if (!(lhi[j] >= llo[j])) { fprintf(stderr, "enclosure inverted at k=%d j=%d\n", k, j); exit(12); }
    }
    if (!ok) { printf("k=%2d: no data\n", k); free(llo); free(lhi); continue; }
    double tot = 0, dt = ldexp(1.0, -DTL);
    for (int j = 0; j < NTV; j++) {
      double ta = ldexp((double)j, -DTL), tb = ldexp((double)(j + 1), -DTL), best = 0;
      for (int cand = 0; cand < 3; cand++) {
        double al, be;
        if (cand == 0) { al = llo[j + 1]; be = 0; }
        else if (cand == 1) { if (j < 2) continue;
          fesetround(FE_DOWNWARD); be = (llo[j] - lhi[j - 1]) / dt; al = llo[j] + ((-be) * ta); }
        else { if (j + 2 > NTV) continue;
          fesetround(FE_UPWARD); be = (lhi[j + 2] - llo[j + 1]) / dt;
          fesetround(FE_DOWNWARD); al = llo[j + 1] + ((-be) * tb); }
        fesetround(FE_UPWARD); double gam_hi = PI_HI - be; fesetround(FE_DOWNWARD);
        const int M = 8; double piece = 0, fprev = flo(ta, sm1, gam_hi, al);
        for (int m = 1; m <= M; m++) {
          double tm = ta + (tb - ta) * m / M, fm = flo(tm, sm1, gam_hi, al);
          piece += ((tb - ta) / M) * sqrt(fprev * fm); fprev = fm;
        }
        if (piece > best) best = piece;
      }
      tot += best;
    }
    tot = tot * 0.5;
    printf("k=%2d: C_k >= %.15e\n", k, tot);
    if (k >= 6) sum6 += tot;
    free(llo); free(lhi);
  }
  printf("sum_{k=6..%d} C_k >= %.15e   (chk_w3: N1 %d N2 %d NT %d, dt 2^-%d, T %d)\n", KMAX, sum6, N1, N2, NT, DTL, TT);
  fesetround(FE_TONEAREST);
}

/* ===== main ===== */
static void setup_grid(void) {
  NR = N1 + N2; ND = 2 * NT - 1; NC = NR * NT;
  arb_init(PI_); arb_const_pi(PI_, PREC); arb_init(DTHA); arb_div_si(DTHA, PI_, NT, PREC);
  DTH = M_PI / NT;
  RBA = _arb_vec_init(NR + 1); RBD = malloc(sizeof(double) * (NR + 1));
  for (int j = 0; j <= NR; j++) {
    if (j <= N1) { arb_set_si(RBA + j, j); arb_div_si(RBA + j, RBA + j, N1, PREC); }
    else { arb_set_si(RBA + j, j - N1); arb_div_si(RBA + j, RBA + j, N2, PREC); arb_add_ui(RBA + j, RBA + j, 1, PREC); }
    RBD[j] = arf_get_d(arb_midref(RBA + j), ARF_RND_NEAR);
  }
}
int main(int argc, char **argv) {
  if (argc >= 2 && !strcmp(argv[1], "--int")) {
    if (argc < 8) { fprintf(stderr, "usage: chk_w3 --int N1 N2 NT DTL T KMAX < PHI\n"); return 1; }
    N1 = atoi(argv[2]); N2 = atoi(argv[3]); NT = atoi(argv[4]); int DTL = atoi(argv[5]), TT = atoi(argv[6]); KMAX = atoi(argv[7]);
    if (!rounding_selftest_all()) { fprintf(stderr, "rounding self-test FAILED\n"); return 10; }
    int NTV = TT << DTL; double *pm[2]; int *pe[2]; char *seen[2];
    for (int p = 0; p < 2; p++) { pm[p] = calloc((size_t)(KMAX + 1) * (NTV + 1), sizeof(double)); pe[p] = calloc((size_t)(KMAX + 1) * (NTV + 1), sizeof(int)); seen[p] = calloc((size_t)(KMAX + 1) * (NTV + 1), 1); }
    char line[512]; long nl = 0;
    while (fgets(line, sizeof line, stdin)) {
      int k, j, pass, e; double m; char ms[128];
      if (sscanf(line, "PHI %d %d %d %127s %d", &k, &j, &pass, ms, &e) != 5) continue;
      m = strtod(ms, NULL);
      if (k < 3 || k > KMAX || j < 1 || j > NTV || pass < 0 || pass > 1) continue;
      size_t q = (size_t)k * (NTV + 1) + j;
      if (seen[pass][q] && (pm[pass][q] != m || pe[pass][q] != e)) { fprintf(stderr, "inconsistent duplicate PHI k=%d j=%d pass=%d\n", k, j, pass); return 16; }
      pm[pass][q] = m; pe[pass][q] = e; seen[pass][q] = 1; nl++;
    }
    for (int k = 3; k <= KMAX; k++) for (int j = 1; j <= NTV; j++) for (int p = 0; p < 2; p++)
      if (!seen[p][(size_t)k * (NTV + 1) + j]) { fprintf(stderr, "missing PHI k=%d j=%d pass=%d\n", k, j, p); return 17; }
    fprintf(stderr, "read %ld PHI lines: complete\n", nl);
    tintegral(DTL, TT, pm, pe);
    return 0;
  }
  if (argc < 8) { fprintf(stderr, "usage: chk_w3 N1 N2 NT DTL T KMAX NTH\n"); return 1; }
  N1 = atoi(argv[1]); N2 = atoi(argv[2]); NT = atoi(argv[3]); int DTL = atoi(argv[4]), TT = atoi(argv[5]); KMAX = atoi(argv[6]); NTH = atoi(argv[7]);
  omp_set_num_threads(NTH); openblas_set_num_threads(1);
  if (!rounding_selftest_all()) { fprintf(stderr, "rounding self-test FAILED\n"); return 10; }
  setup_grid();
  build_auto();
  double t0 = omp_get_wtime();
  if (getenv("CHK3FLOAT")) { FLOATNS = atoi(getenv("CHK3FLOAT")); fprintf(stderr, "FLOAT VALIDATION MODE (not rigorous), NS = %d\n", FLOATNS); }
  per_ring();
  if (FLOATNS) for (int ir = 0; ir < NR; ir++) float_ring(ir);
  pair_tables();
  TS3 = (size_t)NR * NR * NR * ND * ND;
  AB3 = malloc(sizeof(float) * TS3); TCL = malloc(TS3);
  if (!AB3 || !TCL) { fprintf(stderr, "no memory for triple tables (%zu entries)\n", TS3); return 9; }
  const char *ld = getenv("CHK3LOAD"), *sl = getenv("CHK3SLICE");
  int ss = 0, sn = 1; if (sl) sscanf(sl, "%d %d", &ss, &sn);
  if (ld) load_slices(ld);
  else {
    long long nblk = (long long)NR * NR * NR;
    #pragma omp parallel for schedule(dynamic, 1)
    for (long long b = 0; b < nblk; b++) { if (b % sn != ss) continue;
      if (FLOATNS) float_triple_block((int)(b / (NR * NR)), (int)((b / NR) % NR), (int)(b % NR));
      else triple_block((int)(b / (NR * NR)), (int)((b / NR) % NR), (int)(b % NR)); }
    fprintf(stderr, "triple tables (slice %d/%d): %zu entries in %.1f s; far %lld, T=1 %lld, Lemma V fallback %lld, union undecided %lld, min abar3 %.3e\n",
            ss, sn, TS3, omp_get_wtime() - t0, n_far, n_t1, n_lvfail3, n_unfail3, minab3);
    if (getenv("CHK3SAVE")) { save_slice(getenv("CHK3SAVE"), ss, sn); fprintf(stderr, "saved slice %d/%d\n", ss, sn); return 0; }
  }
  for (size_t q = 0; q < TS3; q++) if (TCL[q] != 2 && (!isfinite(AB3[q]) || AB3[q] < 0 || TCL[q] < 0 || TCL[q] > 1)) { fprintf(stderr, "invalid triple entry %zu: abort\n", q); return 13; }
  if (getenv("CHK3TEST")) { long ne = 1000, nsm = 2000; sscanf(getenv("CHK3TEST"), "%ld %ld", &ne, &nsm); selftest(ne, nsm); return 0; }
  KT2 = malloc(sizeof(double) * (size_t)NR * NR * ND); KT3 = malloc(sizeof(float) * TS3); build_tclt();
  if (!KT2 || !KT3) { fprintf(stderr, "no memory for kernels\n"); return 9; }
  int NTV = TT << DTL, j0 = 1, j1 = NTV; const char *jr = getenv("CHK3J"); if (jr) sscanf(jr, "%d %d", &j0, &j1);
  double *pm[2]; int *pe[2];
  for (int p = 0; p < 2; p++) { pm[p] = calloc((size_t)(KMAX + 1) * (NTV + 1), sizeof(double)); pe[p] = calloc((size_t)(KMAX + 1) * (NTV + 1), sizeof(int)); }
  double *phm = malloc(sizeof(double) * (KMAX + 1)); int *phe = malloc(sizeof(int) * (KMAX + 1));
  for (int j = j0; j <= j1; j++) {
    double t = ldexp((double)j, -DTL);
    for (int pass = 0; pass < 2; pass++) {
      recursion(t, pass, phm, phe);
      for (int k = 3; k <= KMAX; k++) {
        pm[pass][(size_t)k * (NTV + 1) + j] = phm[k]; pe[pass][(size_t)k * (NTV + 1) + j] = phe[k];
        printf("PHI %d %d %d %a %d\n", k, j, pass, phm[k], phe[k]);
      }
    }
    fflush(stdout);
    fprintf(stderr, "t = %g done (%.0f s)\n", t, omp_get_wtime() - t0);
  }
  if (j0 == 1 && j1 == NTV) tintegral(DTL, TT, pm, pe);
  return 0;
}
