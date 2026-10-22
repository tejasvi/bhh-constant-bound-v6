chk_w3: independent checker of the window-3 connectivity bound (spec w3/W3.md), frozen-package-ready set
=========================================================================================================

Written from W3.md only (w3/src/w3_arb.c never read). Design differences from the main are listed in the header comment of
src/chk_w3_ede9de74.c: exact support-function S/T classes and distance ranges on polar cells (no pentagons); own union_n
(n = 3, 4); Lemma V with the relative-displacement moments (E[AB] <= sqrt(E A^2) sqrt(E B^2), E B^2 = sum beta_s^2 m_s);
two-sided LV3; own conn automaton (103 states); no mirror trick (every table entry and every (cc, cb) computed directly);
two-pass directed rounding (pass 0 FE_DOWNWARD with kernels rounded down, pass 1 FE_UPWARD with kernels rounded up; no
enclosure factor); own t-integral (extended chord secants of log Phi^disc + GM rule on the log-concave integrand).

RESULT (production grid)
  (N1,N2,NT) = (40,20,96), dt 2^-3, T 6, KMAX 22:
    sum_{k=6..22} C_k >= 3.955730823653845e-03     (main: 3.9174952003e-3; checker / main = 1.00976)
    C_6 >= 1.617416057884107e-03                    (main: 1.6088002734e-3)
  The checker value is >= the main's for every k = 3..22 (int/int_vs_main_40.txt), so the main's claimed bound is
  independently confirmed. (The same PHI lines through --int on a second machine give ...3.955730823653846e-03.)

SOURCES (sha256 prefix)
  src/chk_w3_ede9de74.c         ede9de74686690ee  production source (single file; assembled from c6idea/chk3/*.c)
  build: gcc -O3 -march=native -fopenmp -frounding-math -o chk_w3 chk_w3_ede9de74.c -lflint -lm
         (gcc 14.2.0, FLINT 3.1; binary sha e8a80acfb25ac872, identical on all four production machines)
  val/mcw3dec_17fe2a70.c        17fe2a706baf3870  copy of the main's MC surrogate w3/src/mcw3dec.c, built with -DWIN=3
  diag/chk_w3_abl_7a4d6e1e.c    7a4d6e1e4bc01d66  DIAGNOSTIC ONLY (ablation, see below); = production source + 1 line
  early/chk_w3_434d5348.c       434d534805a9a03b  earlier build (OpenBLAS dense recursion); table code identical to ede9de74

USAGE
  chk_w3 N1 N2 NT DTL T KMAX NTH                     full run (tables, recursion for all t_j, t-integral)
  env CHK3SLICE="s n" CHK3SAVE=f / CHK3LOAD="f1 .."   triple-table slices (blocks b = (ia*NR+ib)*NR+ic with b % n == s)
  env CHK3J="j0 j1"                                  recursion for t_j = j 2^-DTL only; prints "PHI k j pass mantissa exp"
  chk_w3 --int N1 N2 NT DTL T KMAX < PHI             t-integral; checks completeness and that duplicate lines agree
  env CHK3TEST="ne ns [nblk]"                        table self-test (Monte Carlo); nblk > 0: only nblk random blocks
  env CHK3CTL=ab3x|lv3x|tcent|scent|nohalf           NEGATIVE CONTROLS (invalid on purpose)
  env CHK3FLOAT=NS                                   float validation mode (sampled averages, majority classes; NOT rigorous)

PRODUCTION (prod/, int/)
  Each of four machines built one slice (CHK3SLICE/CHK3SAVE), loaded all four after checking their sha256, and computed
  the PHI lines for its range of j: aux03 slice 0 j 1-12; aux04 slice 1 j 13-24; aux05 slice 2 j 24-36; aux06 slice 3
  j 37-48. Slices 14-15 min, recursion 184 s per t-value, all rc 0 (prod/run_*.log, prod/slice_*.err/.sha,
  prod/phi_*.out/.err).
  Cross-machine determinism (j = 24 on aux04 and aux05): all 38 PHI lines for k = 4..22 bitwise identical
  (int/j24_k4to22_w3k*.txt). The k = 3 lines differ by 1-3 ulp: the level-2 closing sum uses an OpenMP reduction whose
  order is unspecified (every order is a valid directed-rounded sum of nonnegative terms; k = 3 is not in the claim).
  int/phi_all.txt (1920 lines, sha fd891cc20f42a190) = all PHI lines with the aux05 copy of j = 24 dropped;
  int/int_dt8.out = chk_w3 --int 40 20 96 3 6 22 < phi_all.txt (rc 0, "read 1920 PHI lines: complete").
  dt coarsening from the same PHI lines (diagnostic): dt 1/4: 3.875507395873255e-03 (main 3.8304e-3);
  dt 1/2: 3.578888872114608e-03 (main 3.2437e-3).

VALIDATION (val/logs/val.log; source ede9de74 unless marked [434d5348])
  Table self-tests (Monte Carlo, every bound and class; z = (bound - mean)/se per entry; thresholds +-5; BAD = 0 in all):
    (40,20,96) production grid, 300 random blocks, 3000 entries x 2000 samples: worst z AB2 -1.65, LV3 -2.98, AB3 -1.37,
      UUP -1.27, ULO +0.53; S=1 tested 1075, T=1 tested 398 (interior + boundary samples), range violations 0  [st40.err]
    (20,10,48) full table, 2000 x 2000: AB2 -0.53, LV3 -4.44, AB3 +0.03, UUP -0.38, ULO -2.04; S=1 779, T=1 241 [434d5348]
    (10,5,24) full table, 3000 x 2000: AB2 2.18, LV3 -7.32, AB3 1.65, UUP 3.96, ULO -5.18; S=1 1043, T=1 309 [434d5348]
  Rigorous runs:
    (10,5,24) KMAX 10: sum_{6..10} >= 1.769937466871392e-03   (main 1.7515166406e-3; +1.05%)
    (20,10,48) KMAX 22: sum_{6..22} >= 3.100996693850987e-03  (main 3.0379534569e-3; +2.07%);
      [434d5348, another machine] 3.100996693851038e-03 (rel. diff 1.6e-14: summation order)
  Negative controls, KMAX 14 (C_6 | sum_{6..14}); every value-producing control raises the value:
    (10,5,24)  base 9.016892e-4 | 1.837664e-3; ab3x (abar3 x 0.97) 9.555876e-4 | 2.002774e-3; tcent (T by centroids)
               1.087542e-3 | 2.303112e-3; scent (S by centroids) 1.281293e-3 | 2.759387e-3; nohalf (value 1 for u = 1)
               1.403901e-3 | 2.854652e-3; lv3x (LV3LO x 1.03): ABORT "negative or invalid abar3 candidate" (guard live)
    (20,10,48) base 1.348281e-3 | 3.073347e-3; ab3x 1.425376e-3 | 3.360185e-3; tcent 1.504873e-3 | 3.535176e-3;
               scent 1.613409e-3 | 3.808376e-3; nohalf 2.042221e-3 | 4.649894e-3; lv3x: ABORT (same guard)
    (main's (10,5,24) control C_6: base 8.977e-4, abar3 x 0.97 9.505e-4, T centroid 1.0729e-3, S centroid 1.2640e-3:
     the checker tracks each within +0.5..1.4%)
  Monte Carlo surrogate (exact positions; mcw3dec -DWIN=3, "conn+deg, A_w"; 32 seeds x 1e6 per k):
    C_6 0.0019469(5), C_7 0.0011707(4), C_8 0.0007278(4)   (main quotes 0.001949, 0.001167, 0.000732)
  Float mode (NS 2, not rigorous): (20,10,48) C_6 1.906498e-3, C_7 1.126738e-3, C_8 6.869207e-4 (main float 1.9090e-3,
    1.1287e-3, 6.8844e-4); (10,5,24) 1.877995e-3, 1.104622e-3, 6.700414e-4 (main 1.8837e-3, 1.1091e-3, 6.7342e-4).
  Ablation (diag/, NOT a claim: sqrt(E B^2) := sqrt(E A^2), i.e. B bounded by A as in the main's X):
    (10,5,24) KMAX 10 sum 1.686922145811541e-03; (20,10,48) KMAX 22 sum 3.013603069463822e-03. So the relative-
    displacement Lemma V is worth +4.9% / +2.9%; without it the checker is 3.7% / 0.8% below the main.

NOTES
  - val.sh passed an empty CHK3LOAD to the (10,5,24) controls and to the (20,10,48) lv3x control ("missing block 0");
    val2.sh / val3.sh reran them (val.log keeps the failed lines; the ctl_* files hold the reruns).
  - Before ede9de74 the pair-table fallback counters were incremented without atomics (counts varied: 5671..5681);
    values were never affected; now atomic (5775 at (20,10,48)).
  - early/: first full (20,10,48) run (r20.*, dense build) and the full-table self-tests (st10.*, st20.*).
  - Tables/slices were not kept (reproducible from source; slice sha256 in prod/slice_*.sha).
