/* w3ind.c: separately written evaluation of the window-3 lower bound for the C_k, k >= 6.
   Written from a working specification of the window-3 bound (W3_<sha8>.md, Sections 0-5: its value function and
   inequality) and Lemmas 3.1 and 3.3 of the first version of the paper, without reading w3_arb.c or chk_w3.c.

   C_k >= (1/2) int t^{k-3/2} e^{-pi t} Phi_k(t) dt, Phi_k(t) = int_{H^{k-1}} val(z) prod_i e^{-t v_i(z)} dz, with
   v_1 = u(|z_1|), v_2 = v2(z_1, z_2) = |B(z_2) \ (B(0) u B(-z_1))|, v_i = v3(z_{i-2}, z_{i-1}, z_i) for i >= 3, and val the
   window-3 connectivity/degree value. Evaluated as follows.
   - Polar cells: NR1 rings on [0,1], NR2 rings on [1,2], NT angular sectors on (-pi/2, pi/2); |z| > 2 dropped.
   - Sure classes: N exact (1 is a ring radius); S(Z,Z') = 1 iff max |z + z'| <= 1 over the cells (exact range, w2ind_geom.h);
     T(Z,Z',Z'') = 1 iff max |z + z' + z''| <= 1, computed as max_psi of the sum of the support functions of the cells
     (w3ind_geom.h). Uncertain adjacencies are treated as absent (val is monotone in the edges).
   - Jensen per product cell with abar >= E v over the product of uniform cells:
       abar2(Z_b, Z_c) = min(E u(|z_c|) upper, A3(c) + E r - (pi + E u(|z_b|))_lower) for (-z_b, 0, z_c);
       abar3(Z_a, Z_b, Z_c) = min(abar2(Z_b, Z_c), E[A4]_up - E[A3]_lo), E[A4]_up = A4(c) + E r4 for
       (-(z_a + z_b), -z_b, 0, z_c), E[A3]_lo = max(A3(c) - E r3 (Lemma V is two-sided), pi + E u(|z_b|) lower);
       c = exact centroids at GPREC bits (the gradient term has mean grad.(C - c), below the margin); Lemma V with the pair
       distance ranges over the convex hulls of the cells (support functions), the moments of the linear displacements, and
       vertex pruning; it needs d- > 0 for every pair with d- < 2, otherwise the fallback is used.
   - Value: w3ind_auto.h (103 encoded states; exhaustively tested against a direct evaluation in w3ind_autotest.c).
   - Recursion at fixed t over (state, previous cell, current cell) in double with directed rounding: kernels
     |Z| e^{-t abar} rounded down (resp. up) with MPFR, all arithmetic in FE_DOWNWARD (resp. FE_UPWARD) on nonnegative numbers.
   - t-integral: on [t_j, t_{j+1}] the best of the right-endpoint value and the two extended secants of the convex
     log Phi^disc, integrated exactly with MPFR's incomplete gamma; [0, t_1] with Phi(t_1); t > T dropped. Printed bounds are
     rounded down.

   Build: gcc -O2 -fopenmp -frounding-math -ffp-contract=off w3ind.c -o w3ind -lmpfr -lgmp -lm
   Usage: w3ind NR1 NR2 NT NSUB KMAX DT T */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <fenv.h>
#include <omp.h>
#include "w3ind_auto.h"
#include "w3ind_geom.h"

#pragma STDC FENV_ACCESS ON
static int NR1, NR2, NR, NT, ND, NSUB, KMAX, NC;
static double DT, TMAX;
static mpfr_t *rr, *area_lo, *area_hi, *czr, *mom;           /* per ring: radii, |Z| bounds, centroid radius, E|z - C|^2 (up) */
static double *eu_up, *eu_lo, *epsr;                           /* per ring: E u(|z|) bounds, sup |z - C| */
static unsigned char *Ncls, *S2, *T3;
static double *ab2, *ab3, *pr_lo, *pr_hi;                   /* pr: |z + z'| over the hull sum, (ring i1 slot 0, ring i2 slot d) */
static long long cnt_lv2 = 0, cnt_lv3 = 0, cnt_lo3 = 0, cnt_t1 = 0;

#define IDX2(ib, ic, d) (((size_t) (ib) * NR + (ic)) * ND + (size_t) ((d) + NT - 1))
#define IDX3(ib, ic, dbc, ia, dab) (((IDX2(ib, ic, dbc)) * NR + (ia)) * ND + (size_t) ((dab) + NT - 1))

static void build_rings(void) {
  NR = NR1 + NR2; NC = NR * NT; ND = 2 * NT - 1;
  rr = malloc(sizeof(mpfr_t) * (NR + 1));
  for (int i = 0; i <= NR; i++) {
    mpfr_init2(rr[i], GPREC);
    if (i <= NR1) { mpfr_set_ui(rr[i], i, MPFR_RNDN); mpfr_div_ui(rr[i], rr[i], NR1, MPFR_RNDN); }
    else { mpfr_set_ui(rr[i], i - NR1, MPFR_RNDN); mpfr_div_ui(rr[i], rr[i], NR2, MPFR_RNDN); mpfr_add_ui(rr[i], rr[i], 1, MPFR_RNDN); }
  }
  mpfr_set_ui(rr[NR1], 1, MPFR_RNDN); mpfr_set_ui(rr[NR], 2, MPFR_RNDN);
  Ncls = malloc(NR); for (int i = 0; i < NR; i++) Ncls[i] = (i < NR1);
  eu_up = malloc(sizeof(double) * NR); eu_lo = malloc(sizeof(double) * NR); epsr = malloc(sizeof(double) * NR);
  area_lo = malloc(sizeof(mpfr_t) * NR); area_hi = malloc(sizeof(mpfr_t) * NR); czr = malloc(sizeof(mpfr_t) * NR); mom = malloc(sizeof(mpfr_t) * NR);
  mpfr_t dth_lo, dth_hi, dth, a, b, w, ua, sw, slo, shi, tt, t2, t3;
  mpfr_inits2(GPREC, dth_lo, dth_hi, dth, a, b, w, ua, sw, slo, shi, tt, t2, t3, (mpfr_ptr) 0);
  mpfr_div_ui(dth_lo, G_PI_LO, NT, MPFR_RNDD); mpfr_div_ui(dth_hi, G_PI_UP, NT, MPFR_RNDU);
  mpfr_const_pi(dth, MPFR_RNDN); mpfr_div_ui(dth, dth, NT, MPFR_RNDN);
  for (int i = 0; i < NR; i++) {
    mpfr_inits2(GPREC, area_lo[i], area_hi[i], czr[i], mom[i], (mpfr_ptr) 0);
    mpfr_sqr(a, rr[i + 1], MPFR_RNDD); mpfr_sqr(b, rr[i], MPFR_RNDU); mpfr_sub(area_lo[i], a, b, MPFR_RNDD);
    mpfr_mul(area_lo[i], area_lo[i], dth_lo, MPFR_RNDD); mpfr_div_2ui(area_lo[i], area_lo[i], 1, MPFR_RNDD);
    mpfr_sqr(a, rr[i + 1], MPFR_RNDU); mpfr_sqr(b, rr[i], MPFR_RNDD); mpfr_sub(area_hi[i], a, b, MPFR_RNDU);
    mpfr_mul(area_hi[i], area_hi[i], dth_hi, MPFR_RNDU); mpfr_div_2ui(area_hi[i], area_hi[i], 1, MPFR_RNDU);
    /* Riemann sums of E u(|z|) (density proportional to r on [r1, r2]) */
    mpfr_set_ui(sw, 0, MPFR_RNDN); mpfr_set_ui(slo, 0, MPFR_RNDN); mpfr_set_ui(shi, 0, MPFR_RNDN);
    for (int q = 0; q < NSUB; q++) {
      mpfr_sub(tt, rr[i + 1], rr[i], MPFR_RNDN); mpfr_mul_ui(a, tt, q, MPFR_RNDN); mpfr_div_ui(a, a, NSUB, MPFR_RNDN); mpfr_add(a, a, rr[i], MPFR_RNDN);
      mpfr_mul_ui(b, tt, q + 1, MPFR_RNDN); mpfr_div_ui(b, b, NSUB, MPFR_RNDN); mpfr_add(b, b, rr[i], MPFR_RNDN);
      if (q == 0) mpfr_set(a, rr[i], MPFR_RNDN);
      if (q == NSUB - 1) mpfr_set(b, rr[i + 1], MPFR_RNDN);
      mpfr_sqr(w, b, MPFR_RNDN); mpfr_sqr(tt, a, MPFR_RNDN); mpfr_sub(w, w, tt, MPFR_RNDN);
      mpfr_add(sw, sw, w, MPFR_RNDN);
      u_dir(ua, a, 0); mpfr_mul(ua, ua, w, MPFR_RNDD); mpfr_add(slo, slo, ua, MPFR_RNDD);
      u_dir(ua, b, 1); mpfr_mul(ua, ua, w, MPFR_RNDU); mpfr_add(shi, shi, ua, MPFR_RNDU);
    }
    mpfr_div(slo, slo, sw, MPFR_RNDD); mpfr_div(shi, shi, sw, MPFR_RNDU);
    mpfr_set_d(tt, 1e-55, MPFR_RNDN); mpfr_sub(slo, slo, tt, MPFR_RNDD); mpfr_add(shi, shi, tt, MPFR_RNDU);
    eu_lo[i] = mpfr_get_d(slo, MPFR_RNDD); eu_up[i] = mpfr_get_d(shi, MPFR_RNDU);
    /* centroid radius (2/3)(r2^3 - r1^3)/(r2^2 - r1^2) sinc(dth/2); E|z - C|^2 = (r1^2 + r2^2)/2 - |C|^2 (+1e-60) */
    mpfr_pow_ui(tt, rr[i + 1], 3, MPFR_RNDN); mpfr_pow_ui(t2, rr[i], 3, MPFR_RNDN); mpfr_sub(tt, tt, t2, MPFR_RNDN);
    mpfr_sqr(t2, rr[i + 1], MPFR_RNDN); mpfr_sqr(t3, rr[i], MPFR_RNDN); mpfr_sub(t2, t2, t3, MPFR_RNDN); mpfr_div(tt, tt, t2, MPFR_RNDN);
    mpfr_mul_ui(tt, tt, 2, MPFR_RNDN); mpfr_div_ui(tt, tt, 3, MPFR_RNDN);
    mpfr_div_2ui(t2, dth, 1, MPFR_RNDN); mpfr_sin(t3, t2, MPFR_RNDN); mpfr_div(t3, t3, t2, MPFR_RNDN); mpfr_mul(czr[i], tt, t3, MPFR_RNDN);
    mpfr_sqr(tt, rr[i], MPFR_RNDN); mpfr_sqr(t2, rr[i + 1], MPFR_RNDN); mpfr_add(tt, tt, t2, MPFR_RNDN); mpfr_div_2ui(tt, tt, 1, MPFR_RNDN);
    mpfr_sqr(t2, czr[i], MPFR_RNDN); mpfr_sub(mom[i], tt, t2, MPFR_RNDN); mpfr_set_d(t2, 1e-60, MPFR_RNDN); mpfr_add(mom[i], mom[i], t2, MPFR_RNDU);
    /* sup |z - C| over the cell: at a corner */
    { double hd = 0.5 * mpfr_get_d(dth, MPFR_RNDN), c0 = mpfr_get_d(czr[i], MPFR_RNDN), ra = mpfr_get_d(rr[i], MPFR_RNDN), rb = mpfr_get_d(rr[i + 1], MPFR_RNDN);
      double e1 = hypot(ra * cos(hd) - c0, ra * sin(hd)), e2 = hypot(rb * cos(hd) - c0, rb * sin(hd));
      epsr[i] = (e1 > e2 ? e1 : e2) * (1 + 1e-12) + 1e-15; }
  }
  mpfr_clears(dth_lo, dth_hi, dth, a, b, w, ua, sw, slo, shi, tt, t2, t3, (mpfr_ptr) 0);
}

/* cell of ring ir at angular slot k: angles [k dth, (k+1) dth]; centroid at the mid angle */
static void set_cell(pcell *c, mpfr_t cx, mpfr_t cy, int ir, int k) {
  mpfr_t d, m; mpfr_inits2(GPREC, d, m, (mpfr_ptr) 0);
  mpfr_const_pi(d, MPFR_RNDN); mpfr_div_ui(d, d, NT, MPFR_RNDN);
  mpfr_set(c->r1, rr[ir], MPFR_RNDN); mpfr_set(c->r2, rr[ir + 1], MPFR_RNDN);
  mpfr_mul_si(c->t1, d, k, MPFR_RNDN); mpfr_mul_si(c->t2, d, k + 1, MPFR_RNDN);
  mpfr_mul_si(m, d, 2 * k + 1, MPFR_RNDN); mpfr_div_2ui(m, m, 1, MPFR_RNDN);
  mpfr_cos(cx, m, MPFR_RNDN); mpfr_mul(cx, cx, czr[ir], MPFR_RNDN);
  mpfr_sin(cy, m, MPFR_RNDN); mpfr_mul(cy, cy, czr[ir], MPFR_RNDN);
  mpfr_clears(d, m, (mpfr_ptr) 0);
}
/* |z| over the hull of a cell of ring ir: [r1 cos(dth/2), r2] (lower rounded down) */
static void single_range(mpfr_t lo, mpfr_t hi, int ir) {
  mpfr_t t; mpfr_init2(t, GPREC);
  mpfr_const_pi(t, MPFR_RNDN); mpfr_div_ui(t, t, 2 * NT, MPFR_RNDN); mpfr_cos(t, t, MPFR_RNDD);
  mpfr_mul(lo, rr[ir], t, MPFR_RNDD); mpfr_set_d(t, 1e-60, MPFR_RNDN); mpfr_sub(lo, lo, t, MPFR_RNDD);
  if (mpfr_sgn(lo) < 0) mpfr_set_ui(lo, 0, MPFR_RNDN);
  mpfr_set(hi, rr[ir + 1], MPFR_RNDN);
  mpfr_clear(t);
}
/* |sum of cells| over the sum of the hulls: hi = rigorous max, lo = max(0, -(upper bound of min support)) - margin */
static void sum_range(mpfr_t lo, mpfr_t hi, pcell *c, int n) {
  mpfr_t t, tp; mpfr_inits2(GPREC, t, tp, (mpfr_ptr) 0);
  h_max_up(hi, c, n);
  h_min_ub(t, c, n); mpfr_neg(lo, t, MPFR_RNDN);
  mpfr_set_d(t, 1e-50, MPFR_RNDN); mpfr_sub(lo, lo, t, MPFR_RNDD);
  if (mpfr_sgn(lo) < 0) mpfr_set_ui(lo, 0, MPFR_RNDN);
  mpfr_clears(t, tp, (mpfr_ptr) 0);
}

/* workspace for one table entry (one per thread) */
typedef struct {
  pcell ca, cb, cc, pc[3];
  mpfr_t px[4], py[4], m[3], dmn[4][4], dmx[4][4], A4, A3, Er4, Er3, t, f, lo3, tmax, ax, ay, bx, by, cx, cy;
} wsp;
static void wsp_init(wsp *w) {
  pcell_init(&w->ca); pcell_init(&w->cb); pcell_init(&w->cc); for (int i = 0; i < 3; i++) pcell_init(&w->pc[i]);
  for (int i = 0; i < 4; i++) { mpfr_init2(w->px[i], GPREC); mpfr_init2(w->py[i], GPREC); for (int j = 0; j < 4; j++) { mpfr_init2(w->dmn[i][j], GPREC); mpfr_init2(w->dmx[i][j], GPREC); } }
  for (int i = 0; i < 3; i++) mpfr_init2(w->m[i], GPREC);
  mpfr_inits2(GPREC, w->A4, w->A3, w->Er4, w->Er3, w->t, w->f, w->lo3, w->tmax, w->ax, w->ay, w->bx, w->by, w->cx, w->cy, (mpfr_ptr) 0);
}
static void wsp_clear(wsp *w) {
  pcell_clear(&w->ca); pcell_clear(&w->cb); pcell_clear(&w->cc); for (int i = 0; i < 3; i++) pcell_clear(&w->pc[i]);
  for (int i = 0; i < 4; i++) { mpfr_clear(w->px[i]); mpfr_clear(w->py[i]); for (int j = 0; j < 4; j++) { mpfr_clear(w->dmn[i][j]); mpfr_clear(w->dmx[i][j]); } }
  for (int i = 0; i < 3; i++) mpfr_clear(w->m[i]);
  mpfr_clears(w->A4, w->A3, w->Er4, w->Er3, w->t, w->f, w->lo3, w->tmax, w->ax, w->ay, w->bx, w->by, w->cx, w->cy, (mpfr_ptr) 0);
}
static void copy_cell(pcell *d, const pcell *s) { mpfr_set(d->r1, s->r1, MPFR_RNDN); mpfr_set(d->r2, s->r2, MPFR_RNDN); mpfr_set(d->t1, s->t1, MPFR_RNDN); mpfr_set(d->t2, s->t2, MPFR_RNDN); }
static void symm(mpfr_t a[4][4], mpfr_t b[4][4], int n) {
  for (int p = 0; p < n; p++) for (int q = p + 1; q < n; q++) { mpfr_set(a[q][p], a[p][q], MPFR_RNDN); mpfr_set(b[q][p], b[p][q], MPFR_RNDN); }
}
typedef struct { int lv; double A, Er, lo, ab; } diag;     /* optional diagnostics */

/* pair entry (Z_b ring ib slot 0, Z_c ring ic slot d): S class and abar2 */
static double pair_entry(wsp *w, int ib, int ic, int d, unsigned char *S, diag *dg) {
  static const lvshape sh2 = {3, 2, {{-1, 0, 0}, {0, 0, 0}, {0, 1, 0}, {0, 0, 0}}};
  frange(w->f, rr[ib], rr[ib + 1], rr[ic], rr[ic + 1], d - 1, d + 1, NT, 1);
  *S = mpfr_cmp_ui(w->f, 1) <= 0;
  double ab = eu_up[ic];
  set_cell(&w->cb, w->bx, w->by, ib, 0); set_cell(&w->cc, w->cx, w->cy, ic, d);
  mpfr_neg(w->px[0], w->bx, MPFR_RNDN); mpfr_neg(w->py[0], w->by, MPFR_RNDN);
  mpfr_set_ui(w->px[1], 0, MPFR_RNDN); mpfr_set_ui(w->py[1], 0, MPFR_RNDN);
  mpfr_set(w->px[2], w->cx, MPFR_RNDN); mpfr_set(w->py[2], w->cy, MPFR_RNDN);
  single_range(w->dmn[0][1], w->dmx[0][1], ib); single_range(w->dmn[1][2], w->dmx[1][2], ic);
  mpfr_set_d(w->dmn[0][2], pr_lo[IDX2(ib, ic, d)], MPFR_RNDN); mpfr_set_d(w->dmx[0][2], pr_hi[IDX2(ib, ic, d)], MPFR_RNDN);   /* |z_b + z_c| */
  symm(w->dmn, w->dmx, 3);
  mpfr_set(w->m[0], mom[ib], MPFR_RNDN); mpfr_set(w->m[1], mom[ic], MPFR_RNDN);
  double eps2[3] = {epsr[ib], epsr[ic], 0};
  int lv = lemmaV_er(w->Er3, &sh2, w->px, w->py, w->m, eps2, w->dmn, w->dmx);
  if (lv) {
    unionN(w->A3, 3, w->px, w->py);
    if (dg) { dg->A = mpfr_get_d(w->A3, MPFR_RNDN); dg->Er = mpfr_get_d(w->Er3, MPFR_RNDU); }
    mpfr_set_d(w->t, GMARGIN, MPFR_RNDN); mpfr_add(w->A3, w->A3, w->t, MPFR_RNDU); mpfr_add(w->A3, w->A3, w->Er3, MPFR_RNDU);
    mpfr_set_d(w->t, eu_lo[ib], MPFR_RNDN); mpfr_add(w->t, w->t, G_PI_LO, MPFR_RNDD); mpfr_sub(w->A3, w->A3, w->t, MPFR_RNDU);
    double v = mpfr_get_d(w->A3, MPFR_RNDU);
    if (v < ab) ab = v;
  }
  if (dg) { dg->lv = lv; dg->ab = ab; }
  if (ab < 0) { fprintf(stderr, "negative abar2 %g at %d %d %d: abort\n", ab, ib, ic, d); exit(5); }
  return ab;
}
/* triple entry (Z_a ring ia slot -dab, Z_b ring ib slot 0, Z_c ring ic slot dbc): T class and abar3 */
static double triple_entry(wsp *w, int ia, int ib, int ic, int dab, int dbc, double fallback, unsigned char *T, int *used, diag *dg) {
  static const lvshape sh4 = {4, 3, {{-1, -1, 0}, {0, -1, 0}, {0, 0, 0}, {0, 0, 1}}};
  static const lvshape sh3 = {3, 2, {{-1, -1, 0}, {0, -1, 0}, {0, 0, 0}, {0, 0, 0}}};
  set_cell(&w->ca, w->ax, w->ay, ia, -dab); set_cell(&w->cb, w->bx, w->by, ib, 0); set_cell(&w->cc, w->cx, w->cy, ic, dbc);
  copy_cell(&w->pc[0], &w->ca); copy_cell(&w->pc[1], &w->cb); copy_cell(&w->pc[2], &w->cc);
  h_max_up(w->tmax, w->pc, 3);                                /* max |z_a + z_b + z_c| */
  *T = mpfr_cmp_ui(w->tmax, 1) <= 0;
  double ab = fallback; used[0] = used[1] = 0;
  /* P0 = -(C_a + C_b), P1 = -C_b, P2 = 0, P3 = C_c */
  mpfr_add(w->px[0], w->ax, w->bx, MPFR_RNDN); mpfr_neg(w->px[0], w->px[0], MPFR_RNDN);
  mpfr_add(w->py[0], w->ay, w->by, MPFR_RNDN); mpfr_neg(w->py[0], w->py[0], MPFR_RNDN);
  mpfr_neg(w->px[1], w->bx, MPFR_RNDN); mpfr_neg(w->py[1], w->by, MPFR_RNDN);
  mpfr_set_ui(w->px[2], 0, MPFR_RNDN); mpfr_set_ui(w->py[2], 0, MPFR_RNDN);
  mpfr_set(w->px[3], w->cx, MPFR_RNDN); mpfr_set(w->py[3], w->cy, MPFR_RNDN);
  single_range(w->dmn[0][1], w->dmx[0][1], ia);               /* |P1 - P0| = |z_a| */
  single_range(w->dmn[1][2], w->dmx[1][2], ib);               /* |z_b| */
  single_range(w->dmn[2][3], w->dmx[2][3], ic);               /* |z_c| */
  mpfr_set_d(w->dmn[0][2], pr_lo[IDX2(ia, ib, dab)], MPFR_RNDN); mpfr_set_d(w->dmx[0][2], pr_hi[IDX2(ia, ib, dab)], MPFR_RNDN);  /* |z_a + z_b| (rotation) */
  mpfr_set_d(w->dmn[1][3], pr_lo[IDX2(ib, ic, dbc)], MPFR_RNDN); mpfr_set_d(w->dmx[1][3], pr_hi[IDX2(ib, ic, dbc)], MPFR_RNDN);  /* |z_b + z_c| */
  mpfr_set(w->dmx[0][3], w->tmax, MPFR_RNDN);                 /* |z_a + z_b + z_c| */
  h_min_ub(w->t, w->pc, 3); mpfr_neg(w->dmn[0][3], w->t, MPFR_RNDN);
  mpfr_set_d(w->t, 1e-50, MPFR_RNDN); mpfr_sub(w->dmn[0][3], w->dmn[0][3], w->t, MPFR_RNDD);
  if (mpfr_sgn(w->dmn[0][3]) < 0) mpfr_set_ui(w->dmn[0][3], 0, MPFR_RNDN);
  symm(w->dmn, w->dmx, 4);
  mpfr_set(w->m[0], mom[ia], MPFR_RNDN); mpfr_set(w->m[1], mom[ib], MPFR_RNDN); mpfr_set(w->m[2], mom[ic], MPFR_RNDN);
  double eps3[3] = {epsr[ia], epsr[ib], epsr[ic]};
  int lv = lemmaV_er(w->Er4, &sh4, w->px, w->py, w->m, eps3, w->dmn, w->dmx);
  if (dg) { dg->lv = lv; dg->A = dg->Er = dg->lo = 0; }
  if (lv) {
    unionN(w->A4, 4, w->px, w->py);
    if (dg) { dg->A = mpfr_get_d(w->A4, MPFR_RNDN); dg->Er = mpfr_get_d(w->Er4, MPFR_RNDU); }
    mpfr_set_d(w->t, GMARGIN, MPFR_RNDN); mpfr_add(w->A4, w->A4, w->t, MPFR_RNDU); mpfr_add(w->A4, w->A4, w->Er4, MPFR_RNDU);
    mpfr_set_d(w->lo3, eu_lo[ib], MPFR_RNDN); mpfr_add(w->lo3, w->lo3, G_PI_LO, MPFR_RNDD);   /* E A3 >= pi + E u(|z_b|) */
    if (lemmaV_er(w->Er3, &sh3, w->px, w->py, w->m, eps3, w->dmn, w->dmx)) {
      unionN(w->A3, 3, w->px, w->py);
      mpfr_set_d(w->t, GMARGIN, MPFR_RNDN); mpfr_sub(w->A3, w->A3, w->t, MPFR_RNDD); mpfr_sub(w->A3, w->A3, w->Er3, MPFR_RNDD);
      if (mpfr_cmp(w->A3, w->lo3) > 0) { mpfr_set(w->lo3, w->A3, MPFR_RNDN); used[1] = 1; }
    }
    if (dg) dg->lo = mpfr_get_d(w->lo3, MPFR_RNDD);
    mpfr_sub(w->A4, w->A4, w->lo3, MPFR_RNDU);
    double v = mpfr_get_d(w->A4, MPFR_RNDU);
    if (v < ab) { ab = v; used[0] = 1; }
  }
  if (dg) dg->ab = ab;
  if (ab < 0) { fprintf(stderr, "negative abar3 %g at %d %d %d %d %d: abort\n", ab, ia, ib, ic, dab, dbc); exit(5); }
  return ab;
}

static void build_pair_ranges(void) {
  size_t n2 = (size_t) NR * NR * ND;
  pr_lo = malloc(sizeof(double) * n2); pr_hi = malloc(sizeof(double) * n2);
  #pragma omp parallel
  {
    pcell pc[2]; pcell_init(&pc[0]); pcell_init(&pc[1]);
    mpfr_t lo, hi, x, y; mpfr_inits2(GPREC, lo, hi, x, y, (mpfr_ptr) 0);
    #pragma omp for schedule(dynamic, 1) collapse(2)
    for (int i1 = 0; i1 < NR; i1++) for (int i2 = 0; i2 < NR; i2++)
      for (int d = -(NT - 1); d <= NT - 1; d++) {
        set_cell(&pc[0], x, y, i1, 0); set_cell(&pc[1], x, y, i2, d);
        sum_range(lo, hi, pc, 2);
        size_t id = IDX2(i1, i2, d);
        pr_lo[id] = mpfr_get_d(lo, MPFR_RNDD); pr_hi[id] = mpfr_get_d(hi, MPFR_RNDU);
      }
    pcell_clear(&pc[0]); pcell_clear(&pc[1]); mpfr_clears(lo, hi, x, y, (mpfr_ptr) 0);
  }
}

static void build_tables(void) {
  size_t n2 = (size_t) NR * NR * ND, n3 = n2 * NR * ND;
  build_pair_ranges();
  ab2 = malloc(sizeof(double) * n2); S2 = malloc(n2);
  ab3 = malloc(sizeof(double) * n3); T3 = malloc(n3);
  if (!ab2 || !S2 || !ab3 || !T3) { fprintf(stderr, "out of memory (tables)\n"); exit(3); }
  #pragma omp parallel
  {
    wsp w; wsp_init(&w);
    long long l_lv2 = 0;
    #pragma omp for schedule(dynamic, 1) collapse(2)
    for (int ib = 0; ib < NR; ib++) for (int ic = 0; ic < NR; ic++)
      for (int d = -(NT - 1); d <= NT - 1; d++) {
        diag dg; size_t id = IDX2(ib, ic, d);
        ab2[id] = pair_entry(&w, ib, ic, d, S2 + id, &dg); l_lv2 += dg.lv && dg.ab < eu_up[ic];
      }
    #pragma omp atomic
    cnt_lv2 += l_lv2;
    wsp_clear(&w);
  }
  /* triples: entries with dbc > 0, or dbc = 0 and dab >= 0; the others by the mirror (dab, dbc) -> (-dab, -dbc) */
  #pragma omp parallel
  {
    wsp w; wsp_init(&w);
    long long l_lv3 = 0, l_lo3 = 0, l_t1 = 0;
    #pragma omp for schedule(dynamic, 1) collapse(3)
    for (int ib = 0; ib < NR; ib++) for (int ic = 0; ic < NR; ic++) for (int dbc = 0; dbc <= NT - 1; dbc++)
      for (int ia = 0; ia < NR; ia++) for (int dab = -(NT - 1); dab <= NT - 1; dab++) {
        if (dbc == 0 && dab < 0) continue;
        size_t id = IDX3(ib, ic, dbc, ia, dab); int used[2];
        ab3[id] = triple_entry(&w, ia, ib, ic, dab, dbc, ab2[IDX2(ib, ic, dbc)], T3 + id, used, NULL);
        l_lv3 += used[0]; l_lo3 += used[1]; l_t1 += T3[id];
      }
    #pragma omp atomic
    cnt_lv3 += l_lv3;
    #pragma omp atomic
    cnt_lo3 += l_lo3;
    #pragma omp atomic
    cnt_t1 += l_t1;
    wsp_clear(&w);
  }
  /* mirror copies; the pair table is then made exactly mirror-symmetric conservatively (maximum; S: 0 on disagreement) */
  for (int ib = 0; ib < NR; ib++) for (int ic = 0; ic < NR; ic++) for (int dbc = -(NT - 1); dbc <= 0; dbc++)
    for (int ia = 0; ia < NR; ia++) for (int dab = -(NT - 1); dab <= NT - 1; dab++) {
      if (dbc == 0 && dab >= 0) continue;
      size_t id = IDX3(ib, ic, dbc, ia, dab), im = IDX3(ib, ic, -dbc, ia, -dab);
      ab3[id] = ab3[im]; T3[id] = T3[im];
    }
  for (int ib = 0; ib < NR; ib++) for (int ic = 0; ic < NR; ic++) for (int d = 1; d <= NT - 1; d++) {
    size_t a = IDX2(ib, ic, d), b = IDX2(ib, ic, -d);
    double m = ab2[a] > ab2[b] ? ab2[a] : ab2[b]; ab2[a] = ab2[b] = m;
    if (S2[a] != S2[b]) S2[a] = S2[b] = 0;
  }
}

/* ---------- recursion at fixed t ---------- */
static double *K2, *K3, *F, *G, *F1v, *NZV;                   /* F, G: [cur][prev][state]; NZV/NZD/NZC: nonzero lists */
static int *F1s; static unsigned char *NZD, *NZC;
static void kernels(double t, int up) {
  size_t n2 = (size_t) NR * NR * ND, n3 = n2 * NR * ND;
  mpfr_rnd_t RD = up ? MPFR_RNDU : MPFR_RNDD;
  #pragma omp parallel
  {
    mpfr_t x, tt; mpfr_init2(x, 80); mpfr_init2(tt, 80);
    mpfr_set_d(tt, t, MPFR_RNDN);
    #pragma omp for schedule(static)
    for (size_t id = 0; id < n3; id++) {
      int ic = (int) ((id / ((size_t) NR * ND * ND)) % NR);
      mpfr_set_d(x, ab3[id], MPFR_RNDN); mpfr_mul(x, x, tt, up ? MPFR_RNDD : MPFR_RNDU); mpfr_neg(x, x, MPFR_RNDN);
      mpfr_exp(x, x, RD); mpfr_mul(x, x, up ? area_hi[ic] : area_lo[ic], RD);
      K3[id] = mpfr_get_d(x, RD);
    }
    #pragma omp for schedule(static)
    for (size_t id = 0; id < n2; id++) {
      int ic = (int) ((id / ND) % NR);
      mpfr_set_d(x, ab2[id], MPFR_RNDN); mpfr_mul(x, x, tt, up ? MPFR_RNDD : MPFR_RNDU); mpfr_neg(x, x, MPFR_RNDN);
      mpfr_exp(x, x, RD); mpfr_mul(x, x, up ? area_hi[ic] : area_lo[ic], RD);
      K2[id] = mpfr_get_d(x, RD);
    }
    #pragma omp for schedule(static)
    for (int c = 0; c < NC; c++) {
      int ir = c / NT;
      mpfr_set_d(x, eu_up[ir], MPFR_RNDN); mpfr_mul(x, x, tt, up ? MPFR_RNDD : MPFR_RNDU); mpfr_neg(x, x, MPFR_RNDN);
      mpfr_exp(x, x, RD); mpfr_mul(x, x, up ? area_hi[ir] : area_lo[ir], RD);
      F1v[c] = mpfr_get_d(x, RD);
      F1s[c] = a3_trans[a3_start][Ncls[ir]][0][0];
    }
    mpfr_clear(x); mpfr_clear(tt);
  }
}
static double closing(const double *H, int up) {               /* sum H * val/2 in the rounding direction */
  int nth = omp_get_max_threads(); double *part = calloc(nth, sizeof(double));
  size_t n = (size_t) NC * NC;
  #pragma omp parallel
  {
    fesetround(up ? FE_UPWARD : FE_DOWNWARD);
    double tot = 0;
    #pragma omp for schedule(static)
    for (size_t q = 0; q < n; q++) for (int D = 0; D < a3_nst; D++) if (a3_close2[D]) tot += H[q * a3_nst + D] * (0.5 * a3_close2[D]);
    part[omp_get_thread_num()] = tot;
    fesetround(FE_TONEAREST);
  }
  fesetround(up ? FE_UPWARD : FE_DOWNWARD);
  double total = 0; for (int q = 0; q < nth; q++) total += part[q];
  fesetround(FE_TONEAREST);
  free(part);
  return total;
}
/* Phi_k(t), k = 3..KMAX, lower (up = 0) or upper (up = 1) */
static void sweep(double t, int up, double *phi) {
  kernels(t, up);
  size_t nF = (size_t) NC * NC * a3_nst;
  /* F_2[c2][c1][D'] */
  memset(F, 0, sizeof(double) * nF);
  #pragma omp parallel
  {
    fesetround(up ? FE_UPWARD : FE_DOWNWARD);
    #pragma omp for schedule(static)
    for (int c2 = 0; c2 < NC; c2++) {
      int i2 = c2 / NT, t2 = c2 % NT;
      for (int c1 = 0; c1 < NC; c1++) {
        int D = F1s[c1]; if (D < 0) continue;
        int i1 = c1 / NT, t1 = c1 % NT;
        size_t id = IDX2(i1, i2, t2 - t1);
        int D2 = a3_trans[D][Ncls[i2]][S2[id]][0]; if (D2 < 0) continue;
        F[((size_t) c2 * NC + c1) * a3_nst + D2] += F1v[c1] * K2[id];
      }
    }
    fesetround(FE_TONEAREST);
  }
  phi[3] = closing(F, up);
  for (int k = 4; k <= KMAX; k++) {                            /* F_{k-2} -> F_{k-1} (adds z_{k-1}) */
    memset(G, 0, sizeof(double) * nF);
    #pragma omp parallel for schedule(static)
    for (size_t q = 0; q < (size_t) NC * NC; q++) {               /* nonzero states of F[cur][prev], cur-major */
      const double *f = F + q * a3_nst; int n = 0;
      for (int D = 0; D < a3_nst; D++) if (f[D] != 0) { NZD[q * a3_nst + n] = (unsigned char) D; NZV[q * a3_nst + n] = f[D]; n++; }
      NZC[q] = (unsigned char) n;
    }
    #pragma omp parallel
    {
      fesetround(up ? FE_UPWARD : FE_DOWNWARD);
      double acc[A3_MAXST];
      #pragma omp for schedule(dynamic, 8)
      for (size_t pr = 0; pr < (size_t) NC * NC; pr++) {
        int cn = (int) (pr / NC), cc = (int) (pr % NC);           /* next, cur */
        int in_ = cn / NT, tn = cn % NT, ic = cc / NT, tc = cc % NT;
        size_t i2 = IDX2(ic, in_, tn - tc);
        int N = Ncls[in_], S = S2[i2];
        for (int D = 0; D < a3_nst; D++) acc[D] = 0;
        int any = 0;
        for (int cp = 0; cp < NC; cp++) {                          /* prev */
          size_t q0 = (size_t) cc * NC + cp; int n = NZC[q0];
          if (!n) continue;
          const unsigned char *nzD = NZD + q0 * a3_nst; const double *nzV = NZV + q0 * a3_nst;
          int ip = cp / NT, tp = cp % NT;
          size_t i3 = IDX3(ic, in_, tn - tc, ip, tc - tp);
          double K = K3[i3]; int T = T3[i3];
          for (int q = 0; q < n; q++) { int D2 = a3_trans[nzD[q]][N][S][T]; if (D2 >= 0) { acc[D2] += nzV[q] * K; any = 1; } }
        }
        if (any) { double *g = G + ((size_t) cn * NC + cc) * a3_nst; for (int D = 0; D < a3_nst; D++) g[D] = acc[D]; }
      }
      fesetround(FE_TONEAREST);
    }
    double *tmp = F; F = G; G = tmp;
    phi[k] = closing(F, up);
  }
}

/* ---------- t-integral (as in w2ind.c) ---------- */
static void piece(mpfr_t out, double s2, double alpha, double beta, double a, double b) {   /* lower bound of int_a^b t^{s-1} e^{alpha + beta t - pi t} */
  mpfr_t g, s, x1, x2, G1, G2, e, gp; mpfr_inits2(128, g, s, x1, x2, G1, G2, e, gp, (mpfr_ptr) 0);
  mpfr_set_d(s, s2, MPFR_RNDN); mpfr_div_2ui(s, s, 1, MPFR_RNDN);
  mpfr_const_pi(g, MPFR_RNDU); mpfr_set_d(x1, beta, MPFR_RNDN); mpfr_sub(g, g, x1, MPFR_RNDU);
  mpfr_set_d(x1, a, MPFR_RNDN); mpfr_mul(x1, x1, g, MPFR_RNDU);
  mpfr_set_d(x2, b, MPFR_RNDN); mpfr_mul(x2, x2, g, MPFR_RNDD);
  if (mpfr_cmp(x1, x2) >= 0) { mpfr_set_ui(out, 0, MPFR_RNDN); goto done; }
  mpfr_gamma_inc(G1, s, x1, MPFR_RNDD); mpfr_gamma_inc(G2, s, x2, MPFR_RNDU);
  mpfr_sub(G1, G1, G2, MPFR_RNDD); if (mpfr_sgn(G1) < 0) mpfr_set_ui(G1, 0, MPFR_RNDN);
  mpfr_neg(gp, s, MPFR_RNDN); mpfr_pow(gp, g, gp, MPFR_RNDD);
  mpfr_set_d(e, alpha, MPFR_RNDN); mpfr_exp(e, e, MPFR_RNDD);
  mpfr_mul(out, G1, gp, MPFR_RNDD); mpfr_mul(out, out, e, MPFR_RNDD);
done:
  mpfr_clears(g, s, x1, x2, G1, G2, e, gp, (mpfr_ptr) 0);
}
static double lgd(double x, int up) {
  mpfr_t y; mpfr_init2(y, 80); mpfr_set_d(y, x, MPFR_RNDN); mpfr_log(y, y, up ? MPFR_RNDU : MPFR_RNDD);
  double r = mpfr_get_d(y, up ? MPFR_RNDU : MPFR_RNDD); mpfr_clear(y); return r;
}

int main(int argc, char **argv) {
  if (argc != 8) { fprintf(stderr, "usage: w3ind NR1 NR2 NT NSUB KMAX DT T\n"); return 2; }
  NR1 = atoi(argv[1]); NR2 = atoi(argv[2]); NT = atoi(argv[3]); NSUB = atoi(argv[4]); KMAX = atoi(argv[5]);
  DT = atof(argv[6]); TMAX = atof(argv[7]);
  if (NR1 < 1 || NR2 < 1 || NT < 2 || NT % 2 || NSUB < 1 || KMAX < 6 || KMAX > 60 || DT <= 0) { fprintf(stderr, "bad parameters\n"); return 2; }
  geom_init();
  double t0 = omp_get_wtime();
  a3_build();
  printf("automaton: window-3 conn+deg value, %d encoded states\n", a3_nst);
  build_rings();
  build_tables();
  { size_t n3 = (size_t) NR * NR * ND * NR * ND; long long nt1 = 0; for (size_t q = 0; q < n3; q++) nt1 += T3[q];
    printf("tables: NR = %d (%d + %d), NT = %d, cells %d; pairs with Lemma V below the fallback %lld of %lld; triples %zu (one mirror half computed): Lemma V below the fallback %lld, two-sided A3 bound used %lld; T sure %lld of all triples (%.0f s)\n",
           NR, NR1, NR2, NT, NC, cnt_lv2, (long long) NR * NR * ND, n3, cnt_lv3, cnt_lo3, nt1, omp_get_wtime() - t0); }
  fflush(stdout);
  size_t n2 = (size_t) NR * NR * ND, n3 = n2 * NR * ND, nF = (size_t) NC * NC * a3_nst;
  K2 = malloc(sizeof(double) * n2); K3 = malloc(sizeof(double) * n3); F1v = malloc(sizeof(double) * NC); F1s = malloc(sizeof(int) * NC);
  F = malloc(sizeof(double) * nF); G = malloc(sizeof(double) * nF);
  NZV = malloc(sizeof(double) * nF); NZD = malloc(nF); NZC = malloc((size_t) NC * NC);
  if (!K2 || !K3 || !F || !G || !NZV || !NZD || !NZC) { fprintf(stderr, "out of memory (recursion)\n"); return 3; }
  int nT = (int) (TMAX / DT + 0.5);
  double *plo = calloc((size_t) (KMAX + 1) * (nT + 1), sizeof(double)), *phi = calloc((size_t) (KMAX + 1) * (nT + 1), sizeof(double));
  double row[64];
  for (int j = 1; j <= nT; j++) {
    double t = DT * j;
    sweep(t, 0, row); for (int k = 3; k <= KMAX; k++) plo[k * (nT + 1) + j] = row[k];
    sweep(t, 1, row); for (int k = 3; k <= KMAX; k++) phi[k * (nT + 1) + j] = row[k];
    printf("t = %.4f: Phi_6 in [%.6e, %.6e] (%.0f s)\n", t, plo[6 * (nT + 1) + j], phi[6 * (nT + 1) + j], omp_get_wtime() - t0); fflush(stdout);
  }
  mpfr_t tot, acc, cand, best; mpfr_inits2(128, tot, acc, cand, best, (mpfr_ptr) 0);
  mpfr_set_ui(tot, 0, MPFR_RNDN);
  for (int k = 3; k <= KMAX; k++) {
    double *L = plo + k * (nT + 1), *U = phi + k * (nT + 1);
    double s2 = 2.0 * k - 1;
    mpfr_set_ui(acc, 0, MPFR_RNDN);
    if (L[1] > 0) { piece(cand, s2, lgd(L[1], 0), 0, 0, DT); mpfr_add(acc, acc, cand, MPFR_RNDD); }
    for (int j = 1; j < nT; j++) {
      double a = DT * j, b = DT * (j + 1);
      mpfr_set_ui(best, 0, MPFR_RNDN);
      if (L[j + 1] > 0) { piece(cand, s2, lgd(L[j + 1], 0), 0, a, b); if (mpfr_cmp(cand, best) > 0) mpfr_set(best, cand, MPFR_RNDN); }
      if (j >= 2 && L[j] > 0 && U[j - 1] > 0) {        /* left secant through t_{j-1}, t_j, extended to the right */
        double lj = lgd(L[j], 0), uj1 = lgd(U[j - 1], 1);
        fesetround(FE_DOWNWARD); double beta = (lj - uj1) / DT; fesetround(FE_TONEAREST);
        fesetround(FE_UPWARD); double pa = beta * a; fesetround(FE_TONEAREST);
        fesetround(FE_DOWNWARD); double alpha = lj - pa; fesetround(FE_TONEAREST);
        piece(cand, s2, alpha, beta, a, b); if (mpfr_cmp(cand, best) > 0) mpfr_set(best, cand, MPFR_RNDN);
      }
      if (j + 2 <= nT && L[j + 1] > 0 && U[j + 2] > 0) {  /* right secant through t_{j+1}, t_{j+2}, extended to the left */
        double lj1 = lgd(L[j + 1], 0), uj2 = lgd(U[j + 2], 1);
        fesetround(FE_UPWARD); double beta = (uj2 - lj1) / DT; fesetround(FE_TONEAREST);
        fesetround(FE_UPWARD); double pb = beta * b; fesetround(FE_TONEAREST);
        fesetround(FE_DOWNWARD); double alpha = lj1 - pb; fesetround(FE_TONEAREST);
        piece(cand, s2, alpha, beta, a, b); if (mpfr_cmp(cand, best) > 0) mpfr_set(best, cand, MPFR_RNDN);
      }
      mpfr_add(acc, acc, best, MPFR_RNDD);
    }
    mpfr_div_2ui(acc, acc, 1, MPFR_RNDD);
    if (k >= 6) mpfr_add(tot, tot, acc, MPFR_RNDD);
    mpfr_printf("k=%2d  C_k >= %.10RDe\n", k, acc);
  }
  mpfr_printf("sum_{k=6..%d} C_k >= %.10RDf   (%.0f s)\n", KMAX, tot, omp_get_wtime() - t0);
  return 0;
}
