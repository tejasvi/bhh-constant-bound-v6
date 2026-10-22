/* w2ind_geom.h: MPFR geometry for w2ind.c (written from the window-2 specification and the first paper only).
   - u bounds with directed rounding;
   - the range of |z + z'|^2 over a pair of polar boxes (own derivation: for fixed radii the value increases with cos(phi);
     for fixed cos it is a convex quadratic in the radii, so the maximum is at a corner and the minimum on an edge);
   - the area of the union of three unit disks at 256 bits (exposed arcs and Green's theorem). */
#ifndef W2GEOM_H
#define W2GEOM_H
#include <mpfr.h>
#include <stdlib.h>
#define GPREC 256
static mpfr_t G_PI_LO, G_PI_UP;
static void geom_init(void) {
  mpfr_inits2(GPREC, G_PI_LO, G_PI_UP, (mpfr_ptr) 0);
  mpfr_const_pi(G_PI_LO, MPFR_RNDD); mpfr_const_pi(G_PI_UP, MPFR_RNDU);
}
/* u(r) for 0 <= r <= 2 (r exact), rounded up (dir = 1) or down (dir = 0) */
static void u_dir(mpfr_t out, const mpfr_t r, int up) {
  mpfr_t h2, t; mpfr_inits2(GPREC, h2, t, (mpfr_ptr) 0);
  mpfr_rnd_t R1 = up ? MPFR_RNDU : MPFR_RNDD, R0 = up ? MPFR_RNDD : MPFR_RNDU;
  mpfr_div_2ui(h2, r, 1, MPFR_RNDN);                       /* exact */
  mpfr_acos(t, h2, R0); mpfr_mul_2ui(t, t, 1, MPFR_RNDN);
  mpfr_sub(out, up ? G_PI_UP : G_PI_LO, t, R1);
  mpfr_sqr(t, r, R0); mpfr_ui_sub(t, 4, t, R1); if (mpfr_sgn(t) < 0) mpfr_set_ui(t, 0, MPFR_RNDN);
  mpfr_sqrt(t, t, R1); mpfr_mul(t, t, h2, R1);
  mpfr_add(out, out, t, R1);
  mpfr_clears(h2, t, (mpfr_ptr) 0);
}
/* bound of min (want_max = 0, rounded down) or max (want_max = 1, rounded up) of f = r^2 + q^2 + 2 r q cos(phi) over
   r in [r1, r2], q in [q1, q2] (all >= 0, exact mpfr), phi in [plo, phi] given by exact multiples kpl, kph of pi/NT
   (|phi| <= pi). */
static void frange(mpfr_t out, const mpfr_t r1, const mpfr_t r2, const mpfr_t q1, const mpfr_t q2, int kpl, int kph, int NT, int want_max) {
  mpfr_t c, a, t, best; mpfr_inits2(GPREC, c, a, t, best, (mpfr_ptr) 0);
  int al = abs(kpl), ah = abs(kph);
  mpfr_rnd_t R = want_max ? MPFR_RNDU : MPFR_RNDD;
  if (want_max) {                                          /* max cos over the range */
    if (kpl <= 0 && kph >= 0) mpfr_set_ui(c, 1, MPFR_RNDN);
    else { int m = al < ah ? al : ah; mpfr_const_pi(a, MPFR_RNDN); mpfr_mul_si(a, a, m, MPFR_RNDN); mpfr_div_si(a, a, NT, MPFR_RNDN);
           /* cos rounded up, with a margin for the rounding of the argument */
           mpfr_cos(c, a, MPFR_RNDU); mpfr_set_d(t, 1e-70, MPFR_RNDN); mpfr_add(c, c, t, MPFR_RNDU); if (mpfr_cmp_ui(c, 1) > 0) mpfr_set_ui(c, 1, MPFR_RNDN); }
  } else {                                                 /* min cos over the range */
    int m = al > ah ? al : ah;
    mpfr_const_pi(a, MPFR_RNDN); mpfr_mul_si(a, a, m, MPFR_RNDN); mpfr_div_si(a, a, NT, MPFR_RNDN);
    mpfr_cos(c, a, MPFR_RNDD); mpfr_set_d(t, 1e-70, MPFR_RNDN); mpfr_sub(c, c, t, MPFR_RNDD); if (mpfr_cmp_si(c, -1) < 0) mpfr_set_si(c, -1, MPFR_RNDN);
  }
  const mpfr_ptr rr[2] = {(mpfr_ptr) r1, (mpfr_ptr) r2}, qq[2] = {(mpfr_ptr) q1, (mpfr_ptr) q2};
  int first = 1;
  #define CAND(RV, QV) do { mpfr_mul(t, RV, QV, R); mpfr_mul(t, t, c, R); mpfr_mul_2ui(t, t, 1, MPFR_RNDN); \
      mpfr_sqr(a, RV, R); mpfr_add(t, t, a, R); mpfr_sqr(a, QV, R); mpfr_add(t, t, a, R); \
      if (first || (want_max ? mpfr_cmp(t, best) > 0 : mpfr_cmp(t, best) < 0)) mpfr_set(best, t, MPFR_RNDN); first = 0; } while (0)
  for (int i = 0; i < 2; i++) for (int j = 0; j < 2; j++) CAND(rr[i], qq[j]);
  if (!want_max) {                                         /* edge minimisers: q* = clamp(-c r) on r = const, and symmetric */
    mpfr_t x; mpfr_init2(x, GPREC);
    for (int i = 0; i < 2; i++) {
      mpfr_mul(x, rr[i], c, MPFR_RNDN); mpfr_neg(x, x, MPFR_RNDN);
      if (mpfr_cmp(x, q1) < 0) mpfr_set(x, q1, MPFR_RNDN); if (mpfr_cmp(x, q2) > 0) mpfr_set(x, q2, MPFR_RNDN);
      CAND(rr[i], x);
      mpfr_mul(x, qq[i], c, MPFR_RNDN); mpfr_neg(x, x, MPFR_RNDN);
      if (mpfr_cmp(x, r1) < 0) mpfr_set(x, r1, MPFR_RNDN); if (mpfr_cmp(x, r2) > 0) mpfr_set(x, r2, MPFR_RNDN);
      CAND(x, qq[i]);
    }
    mpfr_clear(x);
    /* the edge candidates are evaluated at rounded points; the true minimum on an edge can lie below the value at a nearby
       rounded point by at most |grad| * 1e-75: subtract a margin */
    mpfr_set_d(t, 1e-60, MPFR_RNDN); mpfr_sub(best, best, t, MPFR_RNDD);
    if (mpfr_sgn(best) < 0) mpfr_set_ui(best, 0, MPFR_RNDN);
  }
  #undef CAND
  mpfr_set(out, best, MPFR_RNDN);
  mpfr_clears(c, a, t, best, (mpfr_ptr) 0);
}
/* area of the union of unit disks at (x[i], y[i]), i < 3, at GPREC bits (round to nearest); caller adds a margin */
static int cmp_mp(const void *a, const void *b) { return mpfr_cmp(((mpfr_t *) a)[0], ((mpfr_t *) b)[0]); }
static void union3(mpfr_t out, mpfr_t x[3], mpfr_t y[3]) {
  mpfr_t dx, dy, d, ps, al, tp, s1, s2, acc, cur; mpfr_inits2(GPREC, dx, dy, d, ps, al, tp, s1, s2, acc, cur, (mpfr_ptr) 0);
  mpfr_const_pi(tp, MPFR_RNDN); mpfr_mul_2ui(tp, tp, 1, MPFR_RNDN);
  mpfr_set_ui(acc, 0, MPFR_RNDN);
  mpfr_t iv[8][2]; for (int a = 0; a < 8; a++) { mpfr_init2(iv[a][0], GPREC); mpfr_init2(iv[a][1], GPREC); }
  for (int i = 0; i < 3; i++) {
    int m = 0;
    for (int j = 0; j < 3; j++) {
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
    /* sort by start (insertion sort, m <= 4) */
    for (int a = 1; a < m; a++) for (int b = a; b > 0 && mpfr_cmp(iv[b][0], iv[b - 1][0]) < 0; b--) { mpfr_swap(iv[b][0], iv[b - 1][0]); mpfr_swap(iv[b][1], iv[b - 1][1]); }
    mpfr_set_ui(cur, 0, MPFR_RNDN);
    for (int t = 0; t <= m; t++) {
      if (t < m) mpfr_set(s1, iv[t][0], MPFR_RNDN); else mpfr_set(s1, tp, MPFR_RNDN);
      if (mpfr_cmp(s1, cur) > 0) {                         /* exposed arc [cur, s1] */
        /* 0.5 * ((b - a) + x (sin b - sin a) - y (cos b - cos a)) */
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
#endif
