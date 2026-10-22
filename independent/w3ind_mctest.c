/* w3ind_mctest.c: Monte Carlo test of the tables of w3ind.c (compiled in unchanged, main renamed).
   For random entries (half of them restricted to triples whose centroid sum is shorter than 1.6, where the fourth disk
   interacts): abar3 >= mean v3 - 4 se and abar2 >= mean v2 - 4 se over uniform samples of the cells, with exact union areas in
   double by the separate routine of ind_common.h; every sampled point respects the sure classes (S = 1: |z_b + z_c| <= 1,
   T = 1: |z_a + z_b + z_c| <= 1, up to 1e-12). Entries are processed in parallel with one random stream per entry.
   Build: gcc -O2 -fopenmp -frounding-math -ffp-contract=off -I<dir of ind_common.h> w3ind_mctest.c -o w3ind_mctest -lmpfr -lgmp -lm
   Usage: w3ind_mctest NR1 NR2 NT NSUB NENTRIES NSAMPLES SEED */
#define main w3ind_main_unused
#include "w3ind.c"
#undef main
#define MAXK 8
#include "ind_common.h"

typedef struct { uint64_t s[4]; } rng;
static uint64_t rotl64(uint64_t x, int k) { return (x << k) | (x >> (64 - k)); }
static uint64_t rnext(rng *r) { uint64_t *s = r->s, res = rotl64(s[1] * 5, 7) * 9, t = s[1] << 17;
  s[2] ^= s[0]; s[3] ^= s[1]; s[1] ^= s[2]; s[0] ^= s[3]; s[2] ^= t; s[3] = rotl64(s[3], 45); return res; }
static double ru(rng *r) { return (rnext(r) >> 11) * 0x1.0p-53; }
static void rseed(rng *r, uint64_t x) { for (int i = 0; i < 4; i++) { x += 0x9E3779B97F4A7C15ULL; uint64_t z = x;
  z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9ULL; z = (z ^ (z >> 27)) * 0x94D049BB133111EBULL; r->s[i] = z ^ (z >> 31); } }
static void sample_cell(rng *g, int ir, int k, double *x, double *y) {
  double r1 = mpfr_get_d(rr[ir], MPFR_RNDN), r2 = mpfr_get_d(rr[ir + 1], MPFR_RNDN), dth = M_PI / NT;
  double r = sqrt(r1 * r1 + ru(g) * (r2 * r2 - r1 * r1)), th = (k + ru(g)) * dth;
  *x = r * cos(th); *y = r * sin(th);
}
int main(int argc, char **argv) {
  if (argc != 8) { fprintf(stderr, "usage: w3ind_mctest NR1 NR2 NT NSUB NENTRIES NSAMPLES SEED\n"); return 2; }
  NR1 = atoi(argv[1]); NR2 = atoi(argv[2]); NT = atoi(argv[3]); NSUB = atoi(argv[4]);
  int NE = atoi(argv[5]), NS = atoi(argv[6]); uint64_t sd = strtoull(argv[7], 0, 10);
  KMAX = 6; DT = 1; TMAX = 1;
  geom_init(); a3_build(); build_rings(); build_tables();
  printf("tables built: NR %d NT %d; triples with Lemma V below the fallback %lld, two-sided A3 used %lld, T sure %lld (half)\n",
         NR, NT, cnt_lv3, cnt_lo3, cnt_t1);
  long v2viol = 0, v3viol = 0, sviol = 0, tviol = 0, nlv = 0, nnear = 0; double worst2 = -1e9, worst3 = -1e9, gain = 0, slack = 0;
  #pragma omp parallel for schedule(dynamic, 4) reduction(+:v2viol, v3viol, sviol, tviol, nlv, nnear, gain, slack) reduction(max:worst2, worst3)
  for (int e = 0; e < NE; e++) {
    rng g; rseed(&g, sd * 1000003ULL + (uint64_t) e);
    int ia, ib, ic, dab, dbc;
    for (;;) {
      ia = (int) (ru(&g) * NR); ib = (int) (ru(&g) * NR); ic = (int) (ru(&g) * NR);
      dab = (int) (ru(&g) * (2 * NT - 1)) - (NT - 1); dbc = (int) (ru(&g) * (2 * NT - 1)) - (NT - 1);
      if (e % 2 == 0) break;
      double ra = mpfr_get_d(czr[ia], MPFR_RNDN), rb = mpfr_get_d(czr[ib], MPFR_RNDN), rc = mpfr_get_d(czr[ic], MPFR_RNDN), h = M_PI / NT;
      double sx = ra * cos((-dab + 0.5) * h) + rb * cos(0.5 * h) + rc * cos((dbc + 0.5) * h), sy = ra * sin((-dab + 0.5) * h) + rb * sin(0.5 * h) + rc * sin((dbc + 0.5) * h);
      if (hypot(sx, sy) < 1.6) break;
    }
    size_t i3 = IDX3(ib, ic, dbc, ia, dab), i2 = IDX2(ib, ic, dbc);
    double s2 = 0, q2 = 0, s3 = 0, q3 = 0;
    for (int n = 0; n < NS; n++) {
      double ax, ay, bx, by, cx, cy;
      sample_cell(&g, ia, -dab, &ax, &ay); sample_cell(&g, ib, 0, &bx, &by); sample_cell(&g, ic, dbc, &cx, &cy);
      double X4[4] = {-(ax + bx), -bx, 0, cx}, Y4[4] = {-(ay + by), -by, 0, cy};
      double v3 = union_area(4, X4, Y4) - union_area(3, X4, Y4);
      double X3[3] = {-bx, 0, cx}, Y3[3] = {-by, 0, cy};
      double v2 = union_area(3, X3, Y3) - union_area(2, X3, Y3);
      s2 += v2; q2 += v2 * v2; s3 += v3; q3 += v3 * v3;
      if (S2[i2] && hypot(bx + cx, by + cy) > 1 + 1e-12) sviol++;
      if (T3[i3] && hypot(ax + bx + cx, ay + by + cy) > 1 + 1e-12) tviol++;
    }
    double m2 = s2 / NS, se2 = sqrt(fmax(q2 / NS - m2 * m2, 0) / NS), m3 = s3 / NS, se3 = sqrt(fmax(q3 / NS - m3 * m3, 0) / NS);
    double z2 = (m2 - ab2[i2]) / (se2 > 0 ? se2 : 1e-300), z3 = (m3 - ab3[i3]) / (se3 > 0 ? se3 : 1e-300);
    if (ab2[i2] < m2 - 4 * se2) v2viol++;
    if (ab3[i3] < m3 - 4 * se3) v3viol++;
    if (z2 > worst2) worst2 = z2;
    if (z3 > worst3) worst3 = z3;
    if (e % 2) nnear++;
    if (ab3[i3] < ab2[i2]) { nlv++; gain += ab2[i2] - ab3[i3]; slack += ab3[i3] - m3; }
  }
  printf("%d entries x %d samples (%ld with centroid sum < 1.6): abar2 violations %ld (max (mean - abar)/se %.2f), abar3 violations %ld (max %.2f); "
         "sure-class violations S %ld T %ld; entries with abar3 < abar2: %ld (mean gain %.3e, mean abar3 - E v3 %.3e)\n",
         NE, NS, nnear, v2viol, worst2, v3viol, worst3, sviol, tviol, nlv, nlv ? gain / nlv : 0, nlv ? slack / nlv : 0);
  return 0;
}
