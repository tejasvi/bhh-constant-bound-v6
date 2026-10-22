/* chk_level0.c -- independent rigorous evaluation (FLINT/arb) of the LEVEL-0 inequality
 *   C_k >= (1/2) int_0^inf t^{k-3/2} e^{-pi t} m_H(t)^{k-3} P2_H(t) dt,
 *   m_H(t) = int_H e^{-t u(|z|)} dz,  P2_H(t) = int_{H x H} 1[|z1+z2| <= 1] e^{-t(u(|z1|)+u(|z2|))} dz1 dz2,
 *   H = {|z| <= 1, x > 0},  u(d) = pi - 2 acos(d/2) + (d/2) sqrt(4 - d^2).
 * Discretisation DIFFERENT from src/level0_arb.py:
 *   radial cells [a,b]: int_a^b r e^{-t u(r)} dr >= e^{-t u(b)} (b^2-a^2)/2   (u increasing; no Jensen)
 *   angle: phi = theta2 - theta1 in (-pi, pi) with weight (pi - |phi|); a (r1-cell, r2-cell, phi-cell) counts only if
 *     |z1+z2|^2 <= b1^2 + b2^2 + 2 max(r1 r2 cos phi) <= 1 surely; the admissible phi-cells form a final segment
 *     [phi*, pi] (monotone in phi), found by bisection over NPHI cells; weight 2 int_{phi*}^{pi} (pi - phi) = (pi - phi*)^2
 *   t-integral: monotone step bound on a uniform grid (Psi decreasing), exact lower incomplete gamma.
 * usage: chk_level0 NR NPHI DT T KMAX
 */
#include <stdio.h>
#include <stdlib.h>
#include <flint/flint.h>
#include <flint/arb.h>
#include <flint/arb_hypgeom.h>
#define PREC 128
static void ucres(arb_t res, const arb_t d) {   /* u(d) */
  arb_t h, s, pi; arb_init(h); arb_init(s); arb_init(pi);
  arb_const_pi(pi, PREC);
  arb_mul_2exp_si(h, d, -1);            /* d/2 */
  arb_acos(s, h, PREC); arb_mul_2exp_si(s, s, 1);   /* 2 acos(d/2) */
  arb_sub(res, pi, s, PREC);
  arb_mul(s, d, d, PREC); arb_neg(s, s); arb_add_ui(s, s, 4, PREC); arb_sqrt(s, s, PREC); arb_mul(s, s, h, PREC);
  arb_add(res, res, s, PREC);
  arb_clear(h); arb_clear(s); arb_clear(pi);
}
static int surely_inside(slong i, slong j, slong NR, slong c, slong NPHI) {
  /* cell r1 in [i,i+1]/NR, r2 in [j,j+1]/NR, phi in [c, c+1] pi/NPHI: is r1^2+r2^2+2 r1 r2 cos(phi) <= 1 surely? */
  arb_t b1, b2, a1, a2, phia, cphi, mx, t, pi; arb_init(b1); arb_init(b2); arb_init(a1); arb_init(a2); arb_init(phia);
  arb_init(cphi); arb_init(mx); arb_init(t); arb_init(pi);
  arb_const_pi(pi, PREC);
  arb_set_si(a1, i); arb_div_si(a1, a1, NR, PREC); arb_set_si(b1, i + 1); arb_div_si(b1, b1, NR, PREC);
  arb_set_si(a2, j); arb_div_si(a2, a2, NR, PREC); arb_set_si(b2, j + 1); arb_div_si(b2, b2, NR, PREC);
  arb_mul_si(phia, pi, c, PREC); arb_div_si(phia, phia, NPHI, PREC);
  arb_cos(cphi, phia, PREC);
  /* max of r1 r2 cos(phi) over the cell: cos decreasing on [0,pi], max cos at phia;
     if cos(phia) >= 0 use b1 b2 cos(phia), else a1 a2 cos(phia); if the sign is undecided use the larger candidate */
  arb_t m1, m2; arb_init(m1); arb_init(m2);
  arb_mul(m1, b1, b2, PREC); arb_mul(m1, m1, cphi, PREC);
  arb_mul(m2, a1, a2, PREC); arb_mul(m2, m2, cphi, PREC);
  arb_max(mx, m1, m2, PREC);
  arb_mul_2exp_si(mx, mx, 1);
  arb_mul(t, b1, b1, PREC); arb_add(mx, mx, t, PREC); arb_mul(t, b2, b2, PREC); arb_add(mx, mx, t, PREC);
  arb_set_ui(t, 1);
  int ok = arb_le(mx, t);
  arb_clear(m1); arb_clear(m2);
  arb_clear(b1); arb_clear(b2); arb_clear(a1); arb_clear(a2); arb_clear(phia); arb_clear(cphi); arb_clear(mx); arb_clear(t); arb_clear(pi);
  return ok;
}
int main(int argc, char **argv) {
  if (argc < 6) { fprintf(stderr, "usage: chk_level0 NR NPHI DT T KMAX\n"); return 1; }
  slong NR = atol(argv[1]), NPHI = atol(argv[2]); double DTd = atof(argv[3]), Td = atof(argv[4]); int KMAX = atoi(argv[5]);
  slong nT = (slong)(Td / DTd + 0.5);
  arb_t pi, tmp, tmp2; arb_init(pi); arb_init(tmp); arb_init(tmp2); arb_const_pi(pi, PREC);
  /* radial data: w_i = (b^2 - a^2)/2 exact, U_i = upper(u(b_i)) */
  arb_ptr w = _arb_vec_init(NR), U = _arb_vec_init(NR);
  for (slong i = 0; i < NR; i++) {
    arb_set_si(tmp, 2 * i + 1); arb_div_si(tmp, tmp, 2 * NR * NR, PREC); arb_set(w + i, tmp);   /* ((i+1)^2 - i^2)/(2 NR^2) */
    arb_set_si(tmp, i + 1); arb_div_si(tmp, tmp, NR, PREC); ucres(tmp2, tmp);
    arb_set_arf(U + i, arb_midref(tmp2)); arb_add_error_mag(U + i, arb_radref(tmp2));
    { arf_t up; arf_init(up); arb_get_ubound_arf(up, tmp2, PREC); arb_set_arf(U + i, up); arf_clear(up); }
    { arf_t lo; arf_init(lo); arb_get_lbound_arf(lo, w + i, PREC); arb_set_arf(w + i, lo); arf_clear(lo); }
  }
  /* Omega_ij = (pi - phi*_ij)^2 lower bound, phi* = first surely-inside phi-cell start (or none) */
  arb_ptr Om = _arb_vec_init(NR * NR);
  for (slong i = 0; i < NR; i++) for (slong j = i; j < NR; j++) {
    slong lo = 0, hi = NPHI;      /* find smallest c in [0, NPHI) with surely_inside; monotone in c */
    if (!surely_inside(i, j, NR, NPHI - 1, NPHI)) { arb_zero(Om + i * NR + j); arb_zero(Om + j * NR + i); continue; }
    while (lo < hi) { slong mid = (lo + hi) / 2; if (surely_inside(i, j, NR, mid, NPHI)) hi = mid; else lo = mid + 1; }
    /* admissible phi in [lo pi/NPHI, pi]: weight (pi - lo pi / NPHI)^2 */
    arb_mul_si(tmp, pi, NPHI - lo, PREC); arb_div_si(tmp, tmp, NPHI, PREC); arb_mul(tmp, tmp, tmp, PREC);
    { arf_t lb; arf_init(lb); arb_get_lbound_arf(lb, tmp, PREC); arb_set_arf(Om + i * NR + j, lb); arb_set_arf(Om + j * NR + i, lb); arf_clear(lb); }
  }
  fprintf(stderr, "Omega done\n");
  /* t loop */
  arb_ptr M = _arb_vec_init(NR);
  arb_ptr acc = _arb_vec_init(KMAX + 1);
  arb_t t, m, P2, Psi, sk, g0, g1, lw, row; arb_init(t); arb_init(m); arb_init(P2); arb_init(Psi); arb_init(sk); arb_init(g0); arb_init(g1); arb_init(lw); arb_init(row);
  /* previous incomplete gamma values per k: gamma(s, pi t_{j}) */
  arb_ptr gprev = _arb_vec_init(KMAX + 1);
  for (int k = 3; k <= KMAX; k++) arb_zero(gprev + k);
  for (slong jt = 1; jt <= nT; jt++) {
    arb_set_d(t, DTd); arb_mul_si(t, t, jt, PREC);    /* DTd is a dyadic-friendly decimal; t is just a grid point, exactness not needed */
    for (slong i = 0; i < NR; i++) { arb_mul(tmp, t, U + i, PREC); arb_neg(tmp, tmp); arb_exp(tmp, tmp, PREC); arb_mul(M + i, w + i, tmp, PREC); }
    arb_zero(m); for (slong i = 0; i < NR; i++) arb_add(m, m, M + i, PREC); arb_mul(m, m, pi, PREC);
    arb_zero(P2);
    for (slong i = 0; i < NR; i++) { arb_dot(row, NULL, 0, Om + i * NR, 1, M, 1, NR, PREC); arb_addmul(P2, row, M + i, PREC); }
    for (int k = 3; k <= KMAX; k++) {
      arb_pow_ui(Psi, m, k - 3, PREC); arb_mul(Psi, Psi, P2, PREC);
      arb_set_si(sk, 2 * k - 1); arb_mul_2exp_si(sk, sk, -1);       /* s = k - 1/2 */
      arb_mul(tmp, pi, t, PREC); arb_hypgeom_gamma_lower(g1, sk, tmp, 0, PREC);   /* gamma(s, pi t_j) */
      arb_sub(lw, g1, gprev + k, PREC);                                           /* int_{t_{j-1}}^{t_j} ... * pi^s */
      arb_pow(tmp2, pi, sk, PREC); arb_div(lw, lw, tmp2, PREC);
      arb_mul(lw, lw, Psi, PREC);
      arb_add(acc + k, acc + k, lw, PREC);
      arb_set(gprev + k, g1);
    }
  }
  arb_t tot; arb_init(tot); arb_zero(tot);
  for (int k = 3; k <= KMAX; k++) {
    arb_mul_2exp_si(acc + k, acc + k, -1);
    arf_t lb; arf_init(lb); arb_get_lbound_arf(lb, acc + k, PREC);
    printf("k=%2d: C_k >= %.12e\n", k, arf_get_d(lb, ARF_RND_DOWN));
    if (k >= 6) { arb_t q; arb_init(q); arb_set_arf(q, lb); arb_add(tot, tot, q, PREC); arb_clear(q); }
    arf_clear(lb);
  }
  arf_t lb; arf_init(lb); arb_get_lbound_arf(lb, tot, PREC);
  printf("sum_{k=6..%d} C_k >= %.12e\n", KMAX, arf_get_d(lb, ARF_RND_DOWN));
  return 0;
}
