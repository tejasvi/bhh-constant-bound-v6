# Separately written checks

We wrote the programs in this directory separately from the search program, the checker and the window-3
evaluator. They test components of the checker and its leaf bounds against their own implementations, estimate the
true values of `C_k` by Monte Carlo integration, and recompute the window-3 bound for `k >= 6` (section 4). They are
not part of the proof, which rests on the runs of the checker and of the window-3 evaluator alone. Section 4.5 and
Table 2 of the paper summarise their results, and Section 6 uses the Monte Carlo estimates.

Like the checker, the programs number the points from 0: `y_0 = 0`, `y_1 = (r_2, 0)` and `y_j = (xi_j, eta_j)` for
`j >= 2` are the paper's `y_1`, `y_2` and `y_{j+1}`.

| File | Content |
|---|---|
| `ind_common.h` | shared routines: random numbers (xoshiro256\*\*); the exact area of a union of unit disks, from the arcs of its boundary and Green's theorem; the least number `p` of disjoint paths covering a graph, by dynamic programming over pairs (set of vertices, last vertex); `g = p - n_1/2` for connected graphs and `g = 0` for disconnected ones |
| `ind_union.h` | the same union area and table of `g` under prefixed names, for `test_components.c` |
| `test_components.c` | compiles the checker source with its `main` renamed and tests its components (section 1) |
| `patch_dump.py` | writes a copy of the checker that also prints a sample of its leaves with their certified bounds (section 2) |
| `leaf_truth.c` | the integral over each printed leaf, by Gauss-Legendre quadrature or Monte Carlo integration, compared with the bound of the leaf (section 2) |
| `leaves/dump_k3.txt`, `dump_k4.txt`, `dump_k5.txt` | the printed leaves compared for the paper (section 2) |
| `mc_true_ck.c` | Monte Carlo estimate of `C_k` (section 3) |
| `w3ind.c`, `w3ind_auto.h`, `w3ind_geom.h` | separately written evaluation of the window-3 lower bound for the `C_k`, `k >= 6` (section 4) |
| `w2ind_geom.h` | the cell geometry that `w3ind_geom.h` builds on |
| `w3ind_autotest.c` | exhaustive test of the encoding of the window-3 value function in `w3ind_auto.h` (section 4) |
| `w3ind_mctest.c`, `w3ind_geomtest.c` | tests of the tables against sample means and of the support-function bounds (section 4) |
| `w3logs/` | the outputs of the runs of section 4 |

The commands are run in this directory, with the checker at `../checker/chk_ck14.c`. `leaf_truth.c` and
`mc_true_ck.c` need only a C compiler. `test_components.c` and the copy of the checker need OpenMP and FLINT 3, like
the checker, and `patch_dump.py` needs Python 3. `w3ind.c` needs OpenMP and MPFR. The results of sections 1 to 3 were
obtained with gcc 15.2 and FLINT 3.4, and those of section 4 with gcc 14.2 and MPFR 4.2.2, except `w3logs/geomtest.txt` (gcc 15.2, MPFR 4.2.2).

## 1. Components of the checker

    gcc -O2 -fopenmp test_components.c -o test_components -lflint -lmpfr -lgmp -lm
    ./test_components

To compile against a checker source elsewhere, add `-DCHK_SRC='"path/to/chk_ck14.c"'`. For each `k = 3, 4, 5, 6` the
program compares:

- (G) the checker's table of `g` over all edge sets, and its values `gmin`, `gmax` and `g_sigma` (`own_g_bounds2`)
  for about 3,000 random states of the edges, with the dynamic program of `ind_union.h`;
- (R) the ball enclosures of the areas of unions of enlarged disks (`rig_union_R`, Proposition 3.8) at 3,000 random
  configurations, a third of them with two coinciding centres, with the independent union area;
- (E) the function `Phi` of Section 3.5 (`ev_lb`) at 20,000 random inputs with direct evaluation of
  `max(q f^-, V - (1 - q) f^+, 0)`;
- (A) the ball enclosures of `A(c)` and of its gradient (`rig_union`) at 4,000 random configurations, including
  near-tangent pairs, nearly coinciding pairs and three circles through one point, with the independent union area,
  and the gradient with central differences of it;
- (B) the bounds of Lemmas 3.1 and 3.3 as implemented (`rig_remainder`) on 1,200 random boxes, every other one with a
  pair of points at distance close to 2: the inequality `A(y) <= A(c) + grad A(c).(y - c) + R_max` at 20,000 random
  points `y` of each box, and the bounds on the mean and on the root mean square of the remainder against Monte Carlo
  estimates (with 4 standard errors). Boxes for which `rig_union` or `rig_remainder` returns no bound (2 to 13 per cent,
  growing with `k`) are skipped;
- (C) the probability bounds of Section 3.5 (`prob_strips`) for 300 random pairs of rectangles, against a midpoint rule
  for the probability (error about 1e-4);

and once, (D), the distribution functions (`cdf_xy`) at 200,000 inputs, including degenerate intervals and the case
`z = 0` used for order-straddling boxes, against an independent closed form.

Expected: every count of mismatches, violations and differences, and the numbers of refusals in (R) and (A), are 0. The
run takes about two minutes. The output of the run for the paper:

    k=3 (G) g table: 8 edge sets, 0 mismatches vs an independent DP; own_g_bounds2 (gmin, gmax, present/absent, pair states): 3000 random state vectors, 0 mismatches
    k=3 (R) rig_union_R: 3000 configs (1/3 with identical centres), 0 refused; max |A_arb - A_ind| beyond the ball + 1e-12: 0.00e+00
    k=3 (E) ev_lb: 20000 random inputs, 0 differences from max(q fmin, val - (1-q) fmax, 0)
    k=3 (A) union: 4000 configs evaluated, 0 rigorous refusals; max |A_arb - A_ind| beyond the ball radius 0.00e+00; max |grad_x - fd| 1.47e-09
    k=3 (B) Lemma V: 1177 boxes (23 refused), pointwise violations 0 (max excess over Rmax -2.142e-04), E-violations 0 (max E[ex]-Er-4se -7.615e-05), E2-violations 0 (max sqrt E ex+^2 - sEr2 -3.538e-04)
    k=3 (C) staircase: 300 cases, 0 with pin > P + 2e-3 or pout > 1-P + 2e-3; max (pin - P) 0.00e+00, max (pout - (1-P)) 0.00e+00  [P by midpoint rule, error ~1e-4]
    k=4 (G) g table: 64 edge sets, 0 mismatches vs an independent DP; own_g_bounds2 (gmin, gmax, present/absent, pair states): 3000 random state vectors, 0 mismatches
    k=4 (R) rig_union_R: 3000 configs (1/3 with identical centres), 0 refused; max |A_arb - A_ind| beyond the ball + 1e-12: 0.00e+00
    k=4 (E) ev_lb: 20000 random inputs, 0 differences from max(q fmin, val - (1-q) fmax, 0)
    k=4 (A) union: 4000 configs evaluated, 0 rigorous refusals; max |A_arb - A_ind| beyond the ball radius 0.00e+00; max |grad_x - fd| 3.87e-06
    k=4 (B) Lemma V: 1139 boxes (61 refused), pointwise violations 0 (max excess over Rmax -1.996e-04), E-violations 0 (max E[ex]-Er-4se -7.211e-05), E2-violations 0 (max sqrt E ex+^2 - sEr2 -3.233e-04)
    k=4 (C) staircase: 300 cases, 0 with pin > P + 2e-3 or pout > 1-P + 2e-3; max (pin - P) 0.00e+00, max (pout - (1-P)) 0.00e+00  [P by midpoint rule, error ~1e-4]
    k=5 (G) g table: 1024 edge sets, 0 mismatches vs an independent DP; own_g_bounds2 (gmin, gmax, present/absent, pair states): 3000 random state vectors, 0 mismatches
    k=5 (R) rig_union_R: 3000 configs (1/3 with identical centres), 0 refused; max |A_arb - A_ind| beyond the ball + 1e-12: 0.00e+00
    k=5 (E) ev_lb: 20000 random inputs, 0 differences from max(q fmin, val - (1-q) fmax, 0)
    k=5 (A) union: 4000 configs evaluated, 0 rigorous refusals; max |A_arb - A_ind| beyond the ball radius 0.00e+00; max |grad_x - fd| 9.99e-08
    k=5 (B) Lemma V: 1092 boxes (108 refused), pointwise violations 0 (max excess over Rmax -1.570e-03), E-violations 0 (max E[ex]-Er-4se -5.556e-04), E2-violations 0 (max sqrt E ex+^2 - sEr2 -1.272e-03)
    k=5 (C) staircase: 300 cases, 0 with pin > P + 2e-3 or pout > 1-P + 2e-3; max (pin - P) 0.00e+00, max (pout - (1-P)) 0.00e+00  [P by midpoint rule, error ~1e-4]
    k=6 (G) g table: 32768 edge sets, 0 mismatches vs an independent DP; own_g_bounds2 (gmin, gmax, present/absent, pair states): 2968 random state vectors, 0 mismatches
    k=6 (R) rig_union_R: 3000 configs (1/3 with identical centres), 0 refused; max |A_arb - A_ind| beyond the ball + 1e-12: 0.00e+00
    k=6 (E) ev_lb: 20000 random inputs, 0 differences from max(q fmin, val - (1-q) fmax, 0)
    k=6 (A) union: 4000 configs evaluated, 0 rigorous refusals; max |A_arb - A_ind| beyond the ball radius 0.00e+00; max |grad_x - fd| 1.01e-07
    k=6 (B) Lemma V: 1041 boxes (159 refused), pointwise violations 0 (max excess over Rmax -1.780e-03), E-violations 0 (max E[ex]-Er-4se -6.478e-04), E2-violations 0 (max sqrt E ex+^2 - sEr2 -1.337e-03)
    k=6 (C) staircase: 300 cases, 0 with pin > P + 2e-3 or pout > 1-P + 2e-3; max (pin - P) 0.00e+00, max (pout - (1-P)) 0.00e+00  [P by midpoint rule, error ~1e-4]
    (D) run once after the k loop
    (D) cdf_xy vs independent closed form: 200000 cases (incl. degenerate, z = 0 straddle case), 0 differences > 1e-14 beyond the ball, max 0.00e+00

In total: all edge sets for `k <= 6`, 11,968 states of the edges, 16,000 and 12,000 configurations for the union
areas, 80,000 inputs of `Phi`, 4,449 boxes for Lemmas 3.1 and 3.3, 1,200 pairs of rectangles and 200,000 inputs of the
distribution functions.

## 2. Leaf bounds against the integrals over the leaves

`patch_dump.py` writes a copy of the checker that, after computing the certified bound of a leaf, prints the leaf when
a hash of its lower corner is divisible by `N` (environment variable `CHK_DUMP=N`), as a line

    LEAF k lo_0 hi_0 ... lo_{m-1} hi_{m-1} lb L flt F nstr S gmin G gmax H

on standard error, with the box, the certified lower bound `L` of the leaf (before the prefactor), the float value of
the search code, the number of order-straddling pairs and the range of `g` on the leaf. The certified computation is
unchanged. `leaf_truth NGL NMC SEED` reads such lines and computes the integral of `r_2 g A^{-(k-1/2)}` over the part of
each leaf in the domain of Lemma 2.2: by tensor Gauss-Legendre quadrature with `NGL` nodes per coordinate when `g` is
constant on the leaf and no pair straddles it, and otherwise by Monte Carlo integration with `NMC` points. It flags the
leaf as a violation if the bound exceeds the integral (Gauss-Legendre: by a relative 1e-9; Monte Carlo: by 4 standard
errors).

When the bound is positive and fewer than 100 of the `NMC` points fall where the integrand is positive, `leaf_truth`
estimates the integral again with a separate random stream: it samples the leaf until it has found 100 such points (at
most `1000 NMC` samples), takes their bounding box `H`, enlarged by a tenth of the leaf's width on each side and cut to
the leaf, and draws `NMC` points from the mixture of the uniform distributions on the leaf and on `H` with weights 1/2.
This estimator is unbiased for any `H`, because the mixture density is at least half the uniform density on the leaf.
Such leaves are marked `RARE` (`UNRESOLVED` if no positive point is found; none occurred).

The files `leaves/dump_k3.txt`, `leaves/dump_k4.txt` and `leaves/dump_k5.txt` hold the leaves compared for the paper,
sorted with `LC_ALL=C sort`. To compare them:

    gcc -O2 leaf_truth.c -o leaf_truth -lm
    for k in 3 4 5; do mkdir -p parts_k$k; (cd parts_k$k && split -n l/32 -d -a 2 ../leaves/dump_k$k.txt part_); done
    for p in parts_k3/part_??; do ./leaf_truth 8 200000 7 < $p > $p.out & done; wait
    for p in parts_k4/part_??; do ./leaf_truth 6 200000 9 < $p > $p.out & done; wait
    for p in parts_k5/part_??; do ./leaf_truth 5 150000 11 < $p > $p.out & done; wait
    cat parts_k*/part_*.out | grep -c VIOLATION

The output for the paper:

| k | leaves | Gauss-Legendre | Monte Carlo | of these `RARE` | violations | largest bound / integral |
|---|---|---|---|---|---|---|
| 3 | 5,998 | 1,693 | 4,305 | 0 | 0 | 0.9999998 |
| 4 | 2,626 | 1,191 | 1,435 | 20 | 0 | 0.99937 |
| 5 | 1,317 | 135 | 1,182 | 25 | 0 | 0.98899 |

The largest ratios come from Gauss-Legendre leaves for all three k (the largest Monte Carlo ratio for k = 5 is
0.98158). In the most extreme `RARE` case (k = 5) only 1 of the first 150,000 points fell where the integrand is
positive; the bound of that leaf is 3.07e-20 and its integral 9.6e-19.

The files were made as follows, with 32 threads for k = 3 and 4 and 192 threads for k = 5; the copy of the checker
prints the `LEAF` lines in an order that depends on the thread schedule, hence the sorting.

    python3 patch_dump.py ../checker/chk_ck14.c chk_ck14_dump.c
    gcc -O2 -fopenmp chk_ck14_dump.c -o chk_ck14_dump -lflint -lmpfr -lgmp -lm
    # k = 3: a complete run
    CHK_DUMP=2003 ./chk_ck14_dump 3 0.1 0.0002 1e-12 --ninit 4096 2> dump_k3.txt
    # k = 4: four ranges of 24 initial boxes, then random initial boxes, each run limited to 120 s,
    # until there are more than 2,500 leaves
    for lo in 1000 5000 9000 13000; do
      CHK_DUMP=997 ./chk_ck14_dump 4 0.4 0.0005 1e-13 --ninit 16384 --shard $lo $((lo + 24)) 2>> dump_k4.txt; done
    python3 -c "import random; random.seed(12); print(*sorted(random.sample(range(16384), 120)))" > boxes_k4.txt
    for lo in $(cat boxes_k4.txt); do
      CHK_DUMP=997 timeout 120 ./chk_ck14_dump 4 0.4 0.0005 1e-13 --ninit 16384 --shard $lo $((lo + 1)) 2>> dump_k4.txt
      [ $(grep -c LEAF dump_k4.txt) -gt 2500 ] && break; done
    # k = 5 (threshold 3e-13 of the first version; Table 1 now uses 1e-13): eight complete ranges of 32768 initial boxes at N = 2^23
    for s in 0 11 22 30 35 51 56 106; do
      CHK_DUMP=25013 ./chk_ck14_dump 5 0.6 0.00025 3e-13 --ninit 8388608 --shard $((s * 32768)) $(((s + 1) * 32768)) 2>> dump_k5.txt
    done
    for k in 3 4 5; do LC_ALL=C sort dump_k$k.txt > leaves/dump_k$k.txt; done

The time limit stopped the run of the initial box 2708 for k = 4. That run contributed 1,415 of the leaves, and the
leaves that a stopped run prints depend on the machine and the thread schedule. The other leaves come from complete
runs and do not: a later rerun of the complete runs reproduced `dump_k3.txt` and the other 1,211 leaves for k = 4
exactly. The k = 5 file comes from complete runs only (the last range contains no leaf of positive float value). By the
paragraph on `N` in the main README, all these leaves are leaves of the runs of Table 1 (`N` = 16,384 and 8,388,608 lie
in the ranges for k = 4 and 5).

## 3. Monte Carlo estimates of C_k

    gcc -O2 mc_true_ck.c -o mc_true_ck -lm
    for k in 3 4 5 6; do for s in 11 12 13 14 15 16 17 18; do ./mc_true_ck $k 25000000 $s; done; done

The program samples `y_1, ..., y_{k-1}` along a random recursive tree (each new point uniform in the unit disk around
a uniformly chosen earlier point) and divides by the density of this proposal, symmetrised over the orders in which
the points can be added. Each line is an independent estimate with its standard error. The means of the eight runs
for each `k`, with the standard error from the per-run errors, are

    C_3 = 0.0117147(7),   C_4 = 0.0064059(3),   C_5 = 0.0039065(3),   C_6 = 0.0026084(4).

The certified values `C_3 >= 0.0117130195`, `C_4 >= 0.0063707166` and `C_5 >= 0.0035280362` lie below them.

## 4. Separate evaluation of the window-3 bound

`w3ind.c` recomputes the window-3 lower bound for the `C_k`, `k >= 6`. We wrote it from a working specification of the
window-3 bound (its value function and inequality, which Section 5 of the paper states) and from Lemmas 3.1 and 3.3 of the
first version of the paper, without reading `w3_arb.c` or `chk_w3.c`. In the comments of the code, `W3_<sha8>.md` is this
specification. The runs below used 192 cores, except the geometry test, which ran on a small machine; the times are in the logs.

    gcc -O2 w3ind_autotest.c -o w3ind_autotest
    ./w3ind_autotest 10 > w3logs/w3ind_autotest.txt
    gcc -O2 -fopenmp -frounding-math -ffp-contract=off w3ind.c -o w3ind -lmpfr -lgmp -lm
    ./w3ind 10 5 24 32 22 0.125 6 > w3logs/w3ind_10_5_24.txt
    ./w3ind 20 10 48 32 22 0.125 6 > w3logs/w3ind_20_10_48.txt
    gcc -O2 -fopenmp -frounding-math -ffp-contract=off -I. w3ind_mctest.c -o w3ind_mctest -lmpfr -lgmp -lm
    ./w3ind_mctest 10 5 24 32 20000 4000 11 > w3logs/mctest_10_5_24.txt
    ./w3ind_mctest 20 10 48 32 20000 4000 12 > w3logs/mctest_20_10_48.txt
    gcc -O2 -fopenmp -frounding-math -ffp-contract=off w3ind_geomtest.c -o w3ind_geomtest -lmpfr -lgmp -lm
    for g in "4 2 8" "10 5 24" "20 10 48"; do echo "grid $g:"; ./w3ind_geomtest $g 300 7; done > w3logs/geomtest.txt

`w3ind_mctest.c` needs `ind_common.h` of section 1. The arguments of `w3ind` are `NR1 NR2 NT NSUB KMAX DT T`:
- `NR1` rings on [0, 1] and `NR2` rings on [1, 2];
- `NT` angular sectors on the half plane;
- `NSUB` subintervals per ring for the Riemann sums of the mean of `u`;
- `k <= KMAX`;
- the step `DT` in `t` and the cut-off `T`.

The program computes each ingredient its own way:

- The cells are polar boxes with 1 as a ring radius, so `N` is exact.
- The sure classes:
  - `S = 1` if the exact range of `|z + z'|^2` over the two cells is at most 1;
  - `T = 1` if the exact maximum of `|z_a + z_b + z_c|` over the three cells is at most 1. That maximum is computed as
    the largest value of the sum of the cells' support functions.

  An uncertain adjacency is treated as absent.
- The pair bound `abar2(Z_b, Z_c) >= E v2` is the smaller of two bounds:
  - Lemmas 3.1 and 3.3 for the three disks at `(-z_b, 0, z_c)`, minus `pi + E u(|z_b|)` rounded down;
  - the mean of `u(|z_c|)`.
- The triple bound `abar3(Z_a, Z_b, Z_c) >= E v3` is the smaller of two bounds:
  - `abar2(Z_b, Z_c)`;
  - an upper bound of `E A4` minus a lower bound of `E A3`.

  Both use Lemmas 3.1 and 3.3 for the disks at `(-z_a - z_b, -z_b, 0, z_c)`, whose displacements are linear in the
  independent cell offsets:
  - Per pair `(p, q)`, with `chi_pq = |delta_p| + |delta_q|`, the bound
    `E[chi_pq |delta_q - delta_p|] <= (sqrt E|delta_p|^2 + sqrt E|delta_q|^2) sqrt E|delta_q - delta_p|^2` holds,
    and both second moments are exact quadratic forms in the cell moments.
  - The radial part is the smaller of its two bounds.
  - A vertex that stays inside a third disk on the whole product of cells is dropped (Remark 3.2). Its displacement is
    bounded by `eps_p`, the largest `|delta_p|` on the product, plus a rotation bound computed from the largest
    `|delta_q - delta_p|`.
  - `E A3` is bounded below by the two-sided form of the lemma, or by `pi + E u(|z_b|)` rounded down, whichever is
    larger.
  - The distance ranges over the convex hulls of the cells are the exact extremes of sums of support functions.

  Unions of disks are computed at 256 bits. The table geometry runs in round-to-nearest with explicit margins: 1e-45 on
  areas, 1e-50 on support-function values, and a relative 1e-9 on the double-precision pruning test.
- The value function `val(H) = 1{H connected} max(0, 1 - u(H)/2)` with edges at sorted distance 1, 2 and 3 comes from its
  own sliding-window encoding (`w3ind_auto.h`, 103 states).
- The recursion over (state, previous cell, current cell) runs twice in double precision, once with every operation
  rounded down and once rounded up, with the kernels from MPFR rounded the same way.
- On each step `[t_j, t_{j+1}]` the integrand `t^(k-3/2) e^(-pi t) Phi_k(t)` is bounded below by the best of three bounds:
  `Phi_k(t) >= Phi_k(t_{j+1})`, since `Phi_k` decreases in `t`; or one of two lines, since `log Phi_k` is convex in `t`: the
  secant of `log Phi_k` over `[t_{j-1}, t_j]` extended to the right, or the secant over `[t_{j+1}, t_{j+2}]` extended to the left,
  with slopes taken from the lower and upper bounds so that each line stays below `log Phi_k`. On `[0, t_1]` the program uses
  `Phi_k(t_1)`, and it drops `t > T`. Each piece is integrated exactly with the incomplete gamma function of MPFR, rounded
  outward. The printed `C_k` and their sum are rounded down.

Tests:
- `w3ind_autotest` compares the encoding with a direct evaluation (union-find and degrees) on every pattern of sure edges
  for `k <= 10`. It also checks `val(H) <= g` on every graph with at most 7 vertices and counts the states: 103 in all, 99
  in the stationary layer. Expected: 0 mismatches and 0 violations.
- `w3ind_mctest` builds the tables and compares 20,000 random entries with uniform sample means over their cells (4,000
  samples each, exact union areas from `ind_common.h`). Half of the entries are triples whose centroid sum is shorter
  than 1.6, where the fourth disk matters. It also tests the sure classes at every sample. Both grids give 0 violations.
- `w3ind_geomtest` compares the support-function bounds with brute-force extremes over dense samples of the cells: 0
  violations.

Results (`DT` = 2^-3, `T` = 6, `KMAX` = 22, `NSUB` = 32):

| grid `NR1/NR2/NT` | `sum_{k=6..22} C_k >=` | main program, same grid and step |
|---|---|---|
| 10/5/24 | 0.0019858504 | |
| 20/10/48 | 0.0032023178 | 0.0030379534 |

At 20/10/48 this program's value is at least that of the main program (`large/window3/src/w3_arb_093c0f64.c`) for every
`k = 3, ..., 22`. That is observed, not guaranteed; this program uses `NSUB` = 32 against the main program's 64.

`w3ind.c`, `w3ind_auto.h` and `w3ind_geom.h` differ from an earlier copy of the program in comments only. A
comment-stripped diff is empty. The 20/10/48 log and the Monte Carlo logs come from that copy. The 10/5/24 log, the
automaton test and `geomtest.txt` were rerun on the shipped files and reproduce the earlier copy's output exactly, apart
from the times.
