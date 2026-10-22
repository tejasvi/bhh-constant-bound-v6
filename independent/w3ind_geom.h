/* w3ind_geom.h: MPFR geometry for the window-3 evaluator w3ind.c (written from the window-3 specification and Lemmas 3.1/3.3 of
   the first version of the paper).
   - unionN: area of a union of n <= 4 unit disks (covered arcs of each circle, Green's theorem), round to nearest at GPREC;
     every step is continuous in the data, so the caller's margin GMARGIN covers the rounding;
   - support functions of polar cells: h_C(psi) = max_{z in C} (cos psi, sin psi).z, which equals the support function of the
     convex hull of C. For a Minkowski sum S of cells, max |s| over S (and over the sum of the hulls) = max_psi sum_j h_j(psi)
     and dist(0, sum of hulls) >= -sum_j h_j(psi + pi) for every psi (separating direction);
   - Lemma V (Lemmas 3.1/3.3 of the first version of the paper) for n <= 4 points whose displacements are linear in independent cell
     offsets dz_s (E dz_s = 0, E|dz_s|^2 = m_s, |dz_s| <= eps_s). Per potential vertex of a pair (p, q), with M = |d_p| + |d_q|
     and R = |d_q - d_p|, the remainder is at most M [min(c_r R, c0) + min(R/d-, pi)] (c_r = 1/sqrt(4 - d+^2) if d+ < 2), so
     E <= min(c_r E[MR], c0 E M) + min(E[MR]/d-, pi E M) with E M <= sqrt(E|d_p|^2) + sqrt(E|d_q|^2) and
     E[MR] <= (E M bound) sqrt(E R^2) (Minkowski, Cauchy-Schwarz); E|d_p|^2 and E R^2 are exact quadratic forms in the m_s.
     Lemma V bounds the Taylor remainder in absolute value, so the same Er gives a lower bound too. */
#ifndef W3IND_GEOM_H
#define W3IND_GEOM_H
#include "w2ind_geom.h"
#define GMARGIN 1e-45

static void unionN(mpfr_t out, int n, mpfr_t *x, mpfr_t *y) {
  mpfr_t dx, dy, d, ps, al, tp, s1, s2, acc, cur; mpfr_inits2(GPREC, dx, dy, d, ps, al, tp, s1, s2, acc, cur, (mpfr_ptr) 0);
  mpfr_const_pi(tp, MPFR_RNDN); mpfr_mul_2ui(tp, tp, 1, MPFR_RNDN);
  mpfr_set_ui(acc, 0, MPFR_RNDN);
  mpfr_t iv[8][2]; for (int a = 0; a < 8; a++) { mpfr_init2(iv[a][0], GPREC); mpfr_init2(iv[a][1], GPREC); }
  for (int i = 0; i < n; i++) {
    int m = 0;
    for (int j = 0; j < n; j++) {
      if (j == i) continue;
      mpfr_sub(dx, x[j], x[i], MPFR_RNDN); mpfr_sub(dy, y[j], y[i], MPFR_RNDN);
      mpfr_hypot(d, dx, dy, MPFR_RNDN);
      if (mpfr_cmp_ui(d, 2) >= 0) continue;
      mpfr_atan2(ps, dy, dx, MPFR_RNDN);
      mpfr_div_2ui(al, d, 1, MPFR_RNDN); mpfr_acos(al, al, MPFR_RNDN);
      mpfr_sub(s1, ps, al, MPFR_RNDN); mpfr_add(s2, ps, al, MPFR_RNDN);
      while (mpfr_sgn(s1) < 0) { mpfr_add(s1, s1, tp, MPFR_RNDN); mpfr_add(s2, s2, tp, MPFR_RNDN); }
      while (mpfr_cmp(s1, tp) >= 0) { mpfr_sub(s1, s1, tp, MPFR_RNDN); mpfr_sub(s2, s2, tp, MPFR_RNDN); }
      if (mpfr_cmp(s2, tp) > 0) {
        mpfr_set(iv[m][0], s1, MPFR_RNDN); mpfr_set(iv[m][1], tp, MPFR_RNDN); m++;
        mpfr_set_ui(iv[m][0], 0, MPFR_RNDN); mpfr_sub(iv[m][1], s2, tp, MPFR_RNDN); m++;
      } else { mpfr_set(iv[m][0], s1, MPFR_RNDN); mpfr_set(iv[m][1], s2, MPFR_RNDN); m++; }
    }
    for (int a = 1; a < m; a++) for (int b = a; b > 0 && mpfr_cmp(iv[b][0], iv[b - 1][0]) < 0; b--) { mpfr_swap(iv[b][0], iv[b - 1][0]); mpfr_swap(iv[b][1], iv[b - 1][1]); }
    mpfr_set_ui(cur, 0, MPFR_RNDN);
    for (int t = 0; t <= m; t++) {
      if (t < m) mpfr_set(s1, iv[t][0], MPFR_RNDN); else mpfr_set(s1, tp, MPFR_RNDN);
      if (mpfr_cmp(s1, cur) > 0) {                         /* exposed arc [cur, s1]: 0.5 ((b - a) + x (sin b - sin a) - y (cos b - cos a)) */
        mpfr_sub(s2, s1, cur, MPFR_RNDN); mpfr_div_2ui(s2, s2, 1, MPFR_RNDN); mpfr_add(acc, acc, s2, MPFR_RNDN);
        mpfr_sin(d, s1, MPFR_RNDN); mpfr_sin(dx, cur, MPFR_RNDN); mpfr_sub(d, d, dx, MPFR_RNDN); mpfr_mul(d, d, x[i], MPFR_RNDN);
        mpfr_div_2ui(d, d, 1, MPFR_RNDN); mpfr_add(acc, acc, d, MPFR_RNDN);
        mpfr_cos(d, s1, MPFR_RNDN); mpfr_cos(dx, cur, MPFR_RNDN); mpfr_sub(d, d, dx, MPFR_RNDN); mpfr_mul(d, d, y[i], MPFR_RNDN);
        mpfr_div_2ui(d, d, 1, MPFR_RNDN); mpfr_sub(acc, acc, d, MPFR_RNDN);
      }
      if (t < m && mpfr_cmp(iv[t][1], cur) > 0) mpfr_set(cur, iv[t][1], MPFR_RNDN);
    }
  }
  mpfr_set(out, acc, MPFR_RNDN);
  for (int a = 0; a < 8; a++) { mpfr_clear(iv[a][0]); mpfr_clear(iv[a][1]); }
  mpfr_clears(dx, dy, d, ps, al, tp, s1, s2, acc, cur, (mpfr_ptr) 0);
}

/* ---------- support functions of polar cells ---------- */
typedef struct { mpfr_t r1, r2, t1, t2; } pcell;            /* [r1, r2] x [t1, t2], 0 <= r1 < r2, 0 < t2 - t1 < pi */
static void pcell_init(pcell *c) { mpfr_inits2(GPREC, c->r1, c->r2, c->t1, c->t2, (mpfr_ptr) 0); }
static void pcell_clear(pcell *c) { mpfr_clears(c->r1, c->r2, c->t1, c->t2, (mpfr_ptr) 0); }
static void wrap_pi(mpfr_t x) {                             /* reduce to (-pi, pi] */
  mpfr_t tp, p; mpfr_inits2(GPREC, tp, p, (mpfr_ptr) 0);
  mpfr_const_pi(p, MPFR_RNDN); mpfr_mul_2ui(tp, p, 1, MPFR_RNDN);
  while (mpfr_cmp(x, p) > 0) mpfr_sub(x, x, tp, MPFR_RNDN);
  mpfr_neg(p, p, MPFR_RNDN);
  while (mpfr_cmp(x, p) <= 0) mpfr_add(x, x, tp, MPFR_RNDN);
  mpfr_clears(tp, p, (mpfr_ptr) 0);
}
static void wrap_2pi(mpfr_t x) {                            /* reduce to [0, 2 pi) */
  mpfr_t tp; mpfr_init2(tp, GPREC); mpfr_const_pi(tp, MPFR_RNDN); mpfr_mul_2ui(tp, tp, 1, MPFR_RNDN);
  while (mpfr_sgn(x) < 0) mpfr_add(x, x, tp, MPFR_RNDN);
  while (mpfr_cmp(x, tp) >= 0) mpfr_sub(x, x, tp, MPFR_RNDN);
  mpfr_clear(tp);
}
/* upper bound of sum_j h_j(psi) (margins 1e-50 per cell cover the rounding at GPREC) */
static void h_up_at(mpfr_t out, pcell *c, int n, const mpfr_t psi) {
  mpfr_t d1, d2, cc, t, h, acc; mpfr_inits2(GPREC, d1, d2, cc, t, h, acc, (mpfr_ptr) 0);
  mpfr_set_ui(acc, 0, MPFR_RNDN);
  for (int j = 0; j < n; j++) {
    mpfr_sub(d1, psi, c[j].t1, MPFR_RNDN); wrap_pi(d1);
    mpfr_sub(d2, psi, c[j].t2, MPFR_RNDN); wrap_pi(d2);
    if (mpfr_cmp_d(d1, -1e-60) >= 0 && mpfr_cmp_d(d2, 1e-60) <= 0) mpfr_set_ui(cc, 1, MPFR_RNDN);
    else {
      mpfr_cos(cc, d1, MPFR_RNDN); mpfr_cos(t, d2, MPFR_RNDN); if (mpfr_cmp(t, cc) > 0) mpfr_set(cc, t, MPFR_RNDN);
      mpfr_set_d(t, 1e-60, MPFR_RNDN); mpfr_add(cc, cc, t, MPFR_RNDN); if (mpfr_cmp_ui(cc, 1) > 0) mpfr_set_ui(cc, 1, MPFR_RNDN);
    }
    mpfr_mul(h, c[j].r2, cc, MPFR_RNDN); mpfr_mul(t, c[j].r1, cc, MPFR_RNDN); if (mpfr_cmp(t, h) > 0) mpfr_set(h, t, MPFR_RNDN);
    mpfr_add(acc, acc, h, MPFR_RNDN);
    mpfr_set_d(t, 1e-50, MPFR_RNDN); mpfr_add(acc, acc, t, MPFR_RNDN);
  }
  mpfr_set(out, acc, MPFR_RNDN);
  mpfr_clears(d1, d2, cc, t, h, acc, (mpfr_ptr) 0);
}
/* arc decomposition of [0, 2pi) by the breakpoints of all cells; on each open arc every h_j is r2, or R cos(psi - te) */
static int h_breaks(mpfr_t *b, pcell *c, int n) {
  int m = 0; mpfr_t hp; mpfr_init2(hp, GPREC); mpfr_const_pi(hp, MPFR_RNDN); mpfr_div_2ui(hp, hp, 1, MPFR_RNDN);
  for (int j = 0; j < n; j++) {
    mpfr_set(b[m++], c[j].t1, MPFR_RNDN); mpfr_set(b[m++], c[j].t2, MPFR_RNDN);
    mpfr_sub(b[m++], c[j].t1, hp, MPFR_RNDN); mpfr_add(b[m++], c[j].t2, hp, MPFR_RNDN);
    mpfr_add(b[m], c[j].t1, c[j].t2, MPFR_RNDN); mpfr_div_2ui(b[m], b[m], 1, MPFR_RNDN); mpfr_mul_2ui(hp, hp, 1, MPFR_RNDN);
    mpfr_add(b[m], b[m], hp, MPFR_RNDN); mpfr_div_2ui(hp, hp, 1, MPFR_RNDN); m++;
  }
  for (int i = 0; i < m; i++) wrap_2pi(b[i]);
  for (int a = 1; a < m; a++) for (int q = a; q > 0 && mpfr_cmp(b[q], b[q - 1]) < 0; q--) mpfr_swap(b[q], b[q - 1]);
  mpfr_const_pi(hp, MPFR_RNDN); mpfr_mul_2ui(hp, hp, 1, MPFR_RNDN); mpfr_add(b[m], b[0], hp, MPFR_RNDN);   /* closing point */
  mpfr_clear(hp);
  return m;
}
/* form on the arc containing psi_m: H = c0 + A cos psi + B sin psi */
static void h_form(mpfr_t c0, mpfr_t A, mpfr_t B, pcell *c, int n, const mpfr_t pm) {
  mpfr_t d1, d2, x, y, t; mpfr_inits2(GPREC, d1, d2, x, y, t, (mpfr_ptr) 0);
  mpfr_set_ui(c0, 0, MPFR_RNDN); mpfr_set_ui(A, 0, MPFR_RNDN); mpfr_set_ui(B, 0, MPFR_RNDN);
  for (int j = 0; j < n; j++) {
    mpfr_sub(d1, pm, c[j].t1, MPFR_RNDN); wrap_pi(d1);
    mpfr_sub(d2, pm, c[j].t2, MPFR_RNDN); wrap_pi(d2);
    if (mpfr_sgn(d1) >= 0 && mpfr_sgn(d2) <= 0) { mpfr_add(c0, c0, c[j].r2, MPFR_RNDN); continue; }
    mpfr_cos(x, d1, MPFR_RNDN); mpfr_cos(y, d2, MPFR_RNDN);
    int use1 = mpfr_cmp(x, y) >= 0;
    mpfr_srcptr te = use1 ? c[j].t1 : c[j].t2;
    mpfr_srcptr R = mpfr_sgn(use1 ? x : y) >= 0 ? c[j].r2 : c[j].r1;
    mpfr_cos(t, te, MPFR_RNDN); mpfr_mul(t, t, R, MPFR_RNDN); mpfr_add(A, A, t, MPFR_RNDN);
    mpfr_sin(t, te, MPFR_RNDN); mpfr_mul(t, t, R, MPFR_RNDN); mpfr_add(B, B, t, MPFR_RNDN);
  }
  mpfr_clears(d1, d2, x, y, t, (mpfr_ptr) 0);
}
static void h_eval_form(mpfr_t out, const mpfr_t c0, const mpfr_t A, const mpfr_t B, const mpfr_t p) {
  mpfr_t t; mpfr_init2(t, GPREC);
  mpfr_cos(out, p, MPFR_RNDN); mpfr_mul(out, out, A, MPFR_RNDN); mpfr_sin(t, p, MPFR_RNDN); mpfr_mul(t, t, B, MPFR_RNDN);
  mpfr_add(out, out, t, MPFR_RNDN); mpfr_add(out, out, c0, MPFR_RNDN); mpfr_clear(t);
}
/* rigorous upper bound of max_psi sum_j h_j(psi) */
static void h_max_up(mpfr_t out, pcell *c, int n) {
  mpfr_t b[16], pm, c0, A, B, M, ps, v, w, best, L; for (int i = 0; i < 16; i++) mpfr_init2(b[i], GPREC);
  mpfr_inits2(GPREC, pm, c0, A, B, M, ps, v, w, best, L, (mpfr_ptr) 0);
  int m = h_breaks(b, c, n);
  mpfr_set_d(best, -1e9, MPFR_RNDN);
  for (int k = 0; k < m; k++) {
    mpfr_sub(L, b[k + 1], b[k], MPFR_RNDN);
    if (mpfr_cmp_d(L, 1e-40) < 0) {                      /* tiny arc: endpoint values + Lipschitz (|H'| <= sum r2 <= 6) */
      h_up_at(v, c, n, b[k]); h_up_at(w, c, n, b[k + 1]); if (mpfr_cmp(w, v) > 0) mpfr_set(v, w, MPFR_RNDN);
      mpfr_mul_ui(w, L, 6, MPFR_RNDN); mpfr_add(v, v, w, MPFR_RNDN);
    } else {
      mpfr_add(pm, b[k], b[k + 1], MPFR_RNDN); mpfr_div_2ui(pm, pm, 1, MPFR_RNDN);
      h_form(c0, A, B, c, n, pm);
      mpfr_hypot(M, A, B, MPFR_RNDN);
      int interior = 1;
      if (mpfr_cmp_d(M, 1e-50) > 0) {
        mpfr_atan2(ps, B, A, MPFR_RNDN); wrap_2pi(ps);
        mpfr_t lo, hi, tp; mpfr_inits2(GPREC, lo, hi, tp, (mpfr_ptr) 0);
        mpfr_const_pi(tp, MPFR_RNDN); mpfr_mul_2ui(tp, tp, 1, MPFR_RNDN);
        interior = 0;
        for (int sh = -1; sh <= 1; sh++) {               /* psi* + 2 pi sh in [b_k - 1e-40, b_{k+1} + 1e-40] ? */
          mpfr_mul_si(lo, tp, sh, MPFR_RNDN); mpfr_add(lo, lo, ps, MPFR_RNDN);
          mpfr_set_d(hi, 1e-40, MPFR_RNDN);
          mpfr_add(hi, hi, b[k + 1], MPFR_RNDN);
          if (mpfr_cmp(lo, hi) <= 0) { mpfr_set_d(hi, 1e-40, MPFR_RNDN); mpfr_sub(hi, b[k], hi, MPFR_RNDN); if (mpfr_cmp(lo, hi) >= 0) interior = 1; }
        }
        mpfr_clears(lo, hi, tp, (mpfr_ptr) 0);
      }
      if (interior) mpfr_add(v, c0, M, MPFR_RNDN);
      else { h_eval_form(v, c0, A, B, b[k]); h_eval_form(w, c0, A, B, b[k + 1]); if (mpfr_cmp(w, v) > 0) mpfr_set(v, w, MPFR_RNDN); }
      mpfr_set_d(w, 1e-50 * (n + 1), MPFR_RNDN); mpfr_add(v, v, w, MPFR_RNDN);
    }
    if (mpfr_cmp(v, best) > 0) mpfr_set(best, v, MPFR_RNDN);
  }
  mpfr_set(out, best, MPFR_RNDN);
  for (int i = 0; i < 16; i++) mpfr_clear(b[i]);
  mpfr_clears(pm, c0, A, B, M, ps, v, w, best, L, (mpfr_ptr) 0);
}
/* an upper bound of min_psi sum_j h_j(psi): the rigorous value h_up_at at a numerical minimiser */
static void h_min_ub(mpfr_t out, pcell *c, int n) {
  mpfr_t b[16], pm, c0, A, B, M, ps, v, best, arg; for (int i = 0; i < 16; i++) mpfr_init2(b[i], GPREC);
  mpfr_inits2(GPREC, pm, c0, A, B, M, ps, v, best, arg, (mpfr_ptr) 0);
  int m = h_breaks(b, c, n);
  mpfr_set_d(best, 1e9, MPFR_RNDN); mpfr_set(arg, b[0], MPFR_RNDN);
  for (int k = 0; k < m; k++) {
    mpfr_add(pm, b[k], b[k + 1], MPFR_RNDN); mpfr_div_2ui(pm, pm, 1, MPFR_RNDN);
    h_form(c0, A, B, c, n, pm);
    for (int e = 0; e < 3; e++) {                          /* candidates: b_k, b_{k+1}, psi* + pi if inside */
      if (e == 0) mpfr_set(ps, b[k], MPFR_RNDN);
      else if (e == 1) mpfr_set(ps, b[k + 1], MPFR_RNDN);
      else {
        mpfr_hypot(M, A, B, MPFR_RNDN); if (mpfr_cmp_d(M, 1e-50) <= 0) continue;
        mpfr_atan2(ps, B, A, MPFR_RNDN); mpfr_const_pi(v, MPFR_RNDN); mpfr_add(ps, ps, v, MPFR_RNDN); wrap_2pi(ps);
        if (mpfr_cmp(ps, b[k]) < 0) { mpfr_mul_2ui(v, v, 1, MPFR_RNDN); mpfr_add(ps, ps, v, MPFR_RNDN); }
        if (mpfr_cmp(ps, b[k + 1]) > 0) continue;
      }
      h_eval_form(v, c0, A, B, ps);
      if (mpfr_cmp(v, best) < 0) { mpfr_set(best, v, MPFR_RNDN); mpfr_set(arg, ps, MPFR_RNDN); }
    }
  }
  h_up_at(out, c, n, arg);
  for (int i = 0; i < 16; i++) mpfr_clear(b[i]);
  mpfr_clears(pm, c0, A, B, M, ps, v, best, arg, (mpfr_ptr) 0);
}

/* ---------- Lemma V for n <= 4 points with linear displacements ---------- */
typedef struct {
  int n, ns;                    /* points, independent offsets */
  int A[4][3];                  /* integer coefficients: d_p = sum_s A[p][s] dz_s */
} lvshape;
/* Er (upper) for the configuration px, py (centroids, GPREC), offset moments m[s] (upper) and sup eps[s] (upper, double),
   pair distance bounds dmn, dmx over the hull products (n x n, symmetric). Returns 0 if Lemma V is not applicable (a pair
   with d- < 2 and d- <= 0). */
static int lemmaV_er(mpfr_t Er, const lvshape *sh, mpfr_t *px, mpfr_t *py, mpfr_t *m, const double *eps, mpfr_t dmn[4][4], mpfr_t dmx[4][4]) {
  mpfr_t Ep, Eq, EM, ER2, EMR, cr, c0, rad, tan_, t, u; mpfr_inits2(GPREC, Ep, Eq, EM, ER2, EMR, cr, c0, rad, tan_, t, u, (mpfr_ptr) 0);
  int ok = 1;
  mpfr_set_ui(Er, 0, MPFR_RNDN);
  for (int p = 0; p < sh->n && ok; p++) for (int q = p + 1; q < sh->n && ok; q++) {
    if (mpfr_cmp_ui(dmn[p][q], 2) >= 0) continue;
    if (mpfr_sgn(dmn[p][q]) <= 0) { ok = 0; break; }
    mpfr_set_ui(Ep, 0, MPFR_RNDN); mpfr_set_ui(Eq, 0, MPFR_RNDN); mpfr_set_ui(ER2, 0, MPFR_RNDN);
    double delp = 0, delq = 0, Rmax = 0;
    for (int s = 0; s < sh->ns; s++) {
      mpfr_mul_si(t, m[s], sh->A[p][s] * sh->A[p][s], MPFR_RNDU); mpfr_add(Ep, Ep, t, MPFR_RNDU);
      mpfr_mul_si(t, m[s], sh->A[q][s] * sh->A[q][s], MPFR_RNDU); mpfr_add(Eq, Eq, t, MPFR_RNDU);
      int dd = sh->A[q][s] - sh->A[p][s];
      mpfr_mul_si(t, m[s], dd * dd, MPFR_RNDU); mpfr_add(ER2, ER2, t, MPFR_RNDU);
      delp += abs(sh->A[p][s]) * eps[s]; delq += abs(sh->A[q][s]) * eps[s]; Rmax += abs(dd) * eps[s];
    }
    delp = delp * (1 + 1e-12) + 1e-15; delq = delq * (1 + 1e-12) + 1e-15; Rmax = Rmax * (1 + 1e-12) + 1e-15;
    mpfr_sqrt(EM, Ep, MPFR_RNDU); mpfr_sqrt(t, Eq, MPFR_RNDU); mpfr_add(EM, EM, t, MPFR_RNDU);
    mpfr_sqrt(EMR, ER2, MPFR_RNDU); mpfr_mul(EMR, EMR, EM, MPFR_RNDU);
    /* radial: c0 = 2 (asin(min(d+,2)/2) - asin(d-/2)) always; c_r = 1/sqrt(4 - d+^2) when d+ < 2 */
    if (mpfr_cmp_ui(dmx[p][q], 2) >= 0) mpfr_set_ui(t, 1, MPFR_RNDN); else mpfr_div_2ui(t, dmx[p][q], 1, MPFR_RNDU);
    mpfr_asin(t, t, MPFR_RNDU); mpfr_div_2ui(u, dmn[p][q], 1, MPFR_RNDD); mpfr_asin(u, u, MPFR_RNDD);
    mpfr_sub(c0, t, u, MPFR_RNDU); mpfr_mul_2ui(c0, c0, 1, MPFR_RNDU);
    mpfr_mul(rad, c0, EM, MPFR_RNDU);
    int have_cr = mpfr_cmp_ui(dmx[p][q], 2) < 0;
    if (have_cr) {
      mpfr_sqr(t, dmx[p][q], MPFR_RNDU); mpfr_ui_sub(t, 4, t, MPFR_RNDD);
      if (mpfr_sgn(t) > 0) { mpfr_sqrt(t, t, MPFR_RNDD); mpfr_ui_div(cr, 1, t, MPFR_RNDU);
        mpfr_mul(t, cr, EMR, MPFR_RNDU); if (mpfr_cmp(t, rad) < 0) mpfr_set(rad, t, MPFR_RNDN); }
      else have_cr = 0;
    }
    /* tangential: min(E[MR]/d-, pi E M) */
    mpfr_div(tan_, EMR, dmn[p][q], MPFR_RNDU); mpfr_mul(t, G_PI_UP, EM, MPFR_RNDU); if (mpfr_cmp(t, tan_) < 0) mpfr_set(tan_, t, MPFR_RNDN);
    mpfr_add(t, rad, tan_, MPFR_RNDU);
    /* vertex pruning at the centroid configuration */
    int nu = 2;
    {
      double xp = mpfr_get_d(px[p], MPFR_RNDN), yp = mpfr_get_d(py[p], MPFR_RNDN), xq = mpfr_get_d(px[q], MPFR_RNDN), yq = mpfr_get_d(py[q], MPFR_RNDN);
      double dd = hypot(xq - xp, yq - yp);
      if (dd > 1e-9 && dd < 2) {
        double dmd = mpfr_get_d(dmn[p][q], MPFR_RNDD), c0d = mpfr_get_d(c0, MPFR_RNDU);
        double T = c0d;
        if (have_cr) { double crd = mpfr_get_d(cr, MPFR_RNDU); if (crd * Rmax < T) T = crd * Rmax; }
        double tg = Rmax / dmd; if (tg > M_PI) tg = M_PI; T += tg;
        double mx = 0.5 * (xp + xq), my = 0.5 * (yp + yq), hh = sqrt(1 - 0.25 * dd * dd), ux = -(yq - yp) / dd, uy = (xq - xp) / dd;
        for (int sg = -1; sg <= 1; sg += 2) {
          double Px = mx + sg * hh * ux, Py = my + sg * hh * uy;
          int cov = 0;
          for (int l = 0; l < sh->n && !cov; l++) {
            if (l == p || l == q) continue;
            double dell = 0; for (int s = 0; s < sh->ns; s++) dell += abs(sh->A[l][s]) * eps[s];
            dell = dell * (1 + 1e-12) + 1e-15;
            double xl = mpfr_get_d(px[l], MPFR_RNDN), yl = mpfr_get_d(py[l], MPFR_RNDN);
            double margin = hypot(Px - xl, Py - yl) + delp + T + dell;
            if (margin * (1 + 1e-9) + 1e-12 < 1) cov = 1;
          }
          if (cov) nu--;
        }
      }
    }
    mpfr_mul_ui(t, t, nu, MPFR_RNDU);
    mpfr_add(Er, Er, t, MPFR_RNDU);
  }
  mpfr_clears(Ep, Eq, EM, ER2, EMR, cr, c0, rad, tan_, t, u, (mpfr_ptr) 0);
  return ok;
}
#endif
