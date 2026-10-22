# A lower bound of 0.6508 for the Beardwood-Halton-Hammersley constant

Programs, logs and the Lean formalization for the paper *A lower bound of 0.6508 for the Beardwood-Halton-Hammersley
constant* by Tejasvi Singh Tomar (doi:10.5281/zenodo.23554484). They are archived at doi:10.5281/zenodo.23554485.
Earlier versions of this archive:

- doi:10.5281/zenodo.23524862: certified 0.6463 from `C_3`, `C_4` and `C_5` alone.
- doi:10.5281/zenodo.23534690: certified 0.6491 with a weaker bound for the terms with `k >= 6`.
- doi:10.5281/zenodo.23541708: the programs and logs of this version without the Lean proofs.
- doi:10.5281/zenodo.23546916: the Lean proofs of the two weaker bounds for `beta`, but not that of
  `C_5 >= 0.0035280362`.
- doi:10.5281/zenodo.23552638: the same Lean proofs as this version, except that the kernel-only proof gives
  `beta >= 0.6421301`.

## Theorem

Let `beta` be the constant of the Beardwood-Halton-Hammersley theorem. Z. Dong and J. Cao (arXiv:2610.02809, Theorem 3)
proved `beta >= 5/8 + C_3 + ... + C_K` for every `K >= 3`, where

    C_k = Gamma(k - 1/2) / (2 k!) * integral over (R^2)^(k-1) of g(G_1(y)) A(y)^(-(k - 1/2)) dy_2 ... dy_k,   y_1 = 0,

`G_1(y)` is the graph that joins two of the points when their distance is at most 1, `A(y)` is the area of the union of
the unit disks centred at them, and `g` is their path-cover excess. For connected graphs with two to six vertices,
`g = p - n_1/2`, where `p` is the least number of disjoint paths covering the graph and `n_1` the number of vertices of
degree 1. On larger connected graphs, `g = q - n_1/2`, with their lower bound `q >= 1` for `p`. For disconnected graphs,
`g = 0`. The programs in this repository certify

    C_3 >= 0.0117130195,   C_4 >= 0.0063707166,   C_5 >= 0.0035280362,   C_6 + ... + C_22 >= 0.0042404631,

and hence `beta >= 5/8 + 0.0117130195 + 0.0063707166 + 0.0035280362 + 0.0042404631 = 0.6508522354`. The previous lower
bound was 0.6421 (Dong and Cao).

The directory `lean/` holds Lean 4 proofs (Section 6 of the paper) of the bounds for `C_3`, `C_4` and `C_5` of the
theorem, whose checks are evaluated by compiled code (`native_decide`), and of two weaker bounds for `beta`:
`beta >= 0.6491725104`, also with `native_decide`, and `beta >= 0.6426496`, from bounds for `C_3` and `C_4` only,
checked by the Lean kernel alone. They assume Green's formula for the union of the disks and Lemma 3.1 of the paper with
Remark 3.2 and the gradient formula (3.2) in a form along a segment, and the bounds for `beta` also assume Theorem 3 of
Dong and Cao with `K = 30`. The bound 0.6508 rests on the programs above, not on the Lean proofs; the bound for
6 <= k <= 22 is not formalized.

## Method

For k = 3, 4, 5:

1. **Domain.** Put `y_2 = (r_2, 0)` and `y_j = (xi_j, eta_j)`. By symmetry
   `C_k = 2 pi Gamma(k - 1/2) (k-2)!/k! * integral of r_2 g A^(-(k-1/2))` over `r_2 >= 0`, `eta_3 >= 0`,
   `xi_3 <= ... <= xi_k`, and the integrand vanishes outside the box `[0, k-2] x [-(k-2), k-2]^(2k-4)`.
2. **Box bound.** On a box of configurations, `A` is bounded above by its first-order Taylor polynomial at the centre
   plus a remainder controlled by the angular motion of the vertices of the union of the disks, and the integrand is
   averaged over the box (Jensen's inequality). Boxes on which the graph varies, boxes that cross the boundary of the
   ordering constraint and boxes in which two points can coincide get separate bounds (Section 3 of the paper).
3. **Subdivision.** An adaptive bisection splits a box while the estimated loss of its bound exceeds a threshold.
4. **Checker.** The checker repeats the subdivision with a verbatim copy of the search code. On every leaf to which
   the search program assigns a nonzero value it recomputes the bound in ball arithmetic (Arb, part of FLINT), and it
   adds these bounds, clipped below at 0, with rigorous rounding. A leaf of float value 0 is skipped. It then counts
   as 0, which is valid because the integrand is nonnegative, so skipping can only lower the certified sum.

For 6 <= k <= 22 (Section 5 of the paper):

5. **Sorted points.** The points are ordered by their first coordinates, and the integral is written in the
   differences `z_i` of consecutive points. The edges of the graph between points at most three places apart in this
   order form a subgraph. If it is connected, `1 - (number of its vertices of degree < 2)/2` is a lower bound for `g`.
   The area is at most `pi` plus the areas that the disks add, each computed against the three previous disks. After
   a Laplace transform in the area, the integral is an iterated integral of kernels in three consecutive differences.
6. **Evaluation.** `large/window3/src/w3_arb_093c0f64.c` evaluates this bound on polar cells. Its tables are in ball
   arithmetic, its recursion runs in double precision with an explicit relative error bound, and it integrates over
   the Laplace variable exactly with the incomplete gamma function. A second implementation, in `large/window3/chk/`,
   was written from the specification of the bound; at the grid where it was run it gives at least the values of the
   first. `large/level0/` evaluates a weaker bound that keeps only configurations in which consecutive points are joined.

## Contents

| Path | Content |
|---|---|
| `checker/chk_ck14.c` | the checker (C, OpenMP, FLINT ball arithmetic) |
| `search/box_ck14.c` | the search program (double precision; not part of the proof) |
| `checks/pq_check.py` | enumeration showing that `p` equals the lower bound `q` of Dong and Cao for connected graphs with at most six vertices |
| `logs/` | the output of the checker runs of the paper |
| `large/window3/src/` | the evaluation of the bound for 6 <= k <= 22 (files listed below the table) |
| `large/window3/logs/` | the logs of these runs (listed below the table) |
| `large/window3/scripts/` | the scripts that compare the PHI lines of the rerun with those of the run, summarize the counters and write the slice manifest |
| `large/window3/chk/` | the second implementation (`chk_w3`), with its README, logs, validation runs and negative controls |
| `large/level0/` | the evaluation of the weaker bound of Section 5.5 of the paper (`chk_level0.c`, which gives its quoted value, and `level0_arb.py`), a Monte Carlo reference (`mc_level0.c`), logs and negative controls |
| `independent/` | separately written checks, Monte Carlo estimates of `C_k` and a third evaluation of the bound for 6 <= k <= 22, not part of the proof (see `independent/README.md`) |
| `lean/` | the Lean 4 proofs of Section 6 of the paper: `lean/native_v3/` (the bounds for `C_3`, `C_4` and `C_5`), `lean/native/` (`beta >= 0.6491725104`) and `lean/kernel/` (`beta >= 0.6426496`), each with its own README (see the section "Lean proofs" below) |

In `large/window3/src/`, `w3_arb_093c0f64.c` gives the quoted value. `w3_arb_a32632cb.c`, `w3_arb_ed91d98d.c` and
`w3_arb_3e8d8aeb.c` produced the runs at the coarser grids (40,20,96), (30,15,72) and (20,10,48). `w3_arb_7e03aba8.c` is
the same program with diagnostic switches. The table `w3conn_auto.h` of the one-pass value computation is generated by
`wconn_gen.py` and tested by `wconntest.py`, `w3test.py` and `w3enum.py`. `w3_tabletest.c` is the table test, and
`mcw3dec.c` is the Monte Carlo reference. `w3_arb_inst_d21d8507.c` is the copy with underflow counters that
`make_inst_4f3a7d46.py` makes from `w3_arb_093c0f64.c`.

In `large/window3/logs/`, `cert60/` holds the quoted run: slice logs and hashes, PHI lines, `combined_60_30_144.txt`,
`SLICE_MANIFEST.txt`, and the rerun with counters in `t60inst/`, compared with the run in `PHI_COMPARE.txt`. `cert40/`
and `cert_w3a/` hold the runs at the coarser grids and the diagnostic runs, and `ctl093/` holds negative controls and
the table test.

The checker contains lines 27-399 of `search/box_ck14.c` verbatim, marked in its source, with inserted observation
lines marked CHK. For the same number of initial boxes, or any `N` in the ranges given below, it therefore visits the
same leaves as the search program.

Notes on the sources. The programs are released as they were run, apart from the two changes listed first, so some of
their comments use earlier names, cite working files that are not included, or describe an earlier design. The
correspondences are as follows.

- Changed files. `search/box_ck14.c` differs from the file that the checker's comments name,
  `chk/box_ck14_snapshot.c` (sha256 6feb4deb...), only in its header comment, lines 1-20. In `large/window3/`, the logs
  and `chk/README.txt` name the machines by neutral labels (`machine-01` to `machine-24`, `aux-01` to `aux-06`), storage
  locations and machine details are left out, and the scripts that copied files between machines are not included
  (`chk/README.txt` still mentions one of them, `val.sh`). `chk/SHA256SUMS` lists the files of `chk/` as shipped.
- Specifications that are not included. The paper states the bounds. The checker's comments cite the sections of
  `BOUNDS.md`: 3a = Lemmas 3.1 and 3.3 (vertex remainder and its moments), 3b = Proposition 3.4 (averaged bound),
  3c = Lemma 3.5 and Proposition 3.6 (undetermined edges), 3d = Proposition 3.7 (order-straddling boxes),
  3e = Proposition 3.8 (coinciding points). The programs in `large/window3/` cite `W3.md`: section 2 is Lemmas 5.2 and
  5.3, section 3 is Lemma 5.4, section 4 is the recursion of Section 5.4, and sections 5.1-5.7 are the discretization
  of Section 5.4 (5.5 with Lemma 5.5, 5.6 the rounding and 5.7 the integral over `t`). "Lemma V" is Lemmas 3.1 and 3.3,
  in the linear form of Lemma 5.5. The programs in `large/level0/` cite `LEVEL0.md`, which is Section 5.5.
- Earlier names. The sources in `large/window3/src/` call themselves `w3_arb.c`. `w3_tabletest.c` includes `w3_arb.c`,
  so copy `w3_arb_093c0f64.c` to `w3_arb.c` before building it. `src/level0_arb.py` is `large/level0/level0_arb.py`.
- Notation. Both programs for k <= 5 number the points from 0: their `y_0, y_1, y_j` are the paper's
  `y_1, y_2, y_{j+1}`. In `w3_arb.c`, `u(r)` is `A_1(r)`, `abar2` and `abar3` are `a_2` and `a_3` with bars, `LV3LO` is
  the lower bound for the mean of the area of three disks that enters `abar3`, `PHI` is `Psi_k^d`, `N`, `S` and `T` are
  the edges `{i+1, i}`, `{i+1, i-1}` and `{i+1, i-2}`, and "Lemma 4" is the range of `|z + z'|^2` over a pair of cells.
- Unused output and modes. The checker also prints a second value from a variant of 3b ("tighter valid 3b variant");
  this value is not used. `w3_arb.c` has a mode that rounds its kernels to single precision; the quoted run did not use
  it. It also has a validation mode, `W3FLOAT`, which is not rigorous, and negative controls, `W3CTRL`.

## Building

    gcc -O2 -fopenmp -DCHK_BUILD="\"$(sha256sum checker/chk_ck14.c | cut -c1-16)\"" checker/chk_ck14.c \
        -o chk_ck14 -lflint -lmpfr -lgmp -lm

The checker needs FLINT 3 (tested with 3.1 and 3.4) and a C compiler with OpenMP (tested with gcc 14 and 15). The
build id printed in every output line is the first 16 hex digits of the SHA-256 of `checker/chk_ck14.c`. The search
program is built and run with

    gcc -O2 -fopenmp search/box_ck14.c -o box_ck14 -lm
    ./box_ck14 K W0 WF EPS

The programs for 6 <= k <= 22 are built with

    cd large/window3/src
    gcc -O3 -march=x86-64-v3 -ffp-contract=off -fopenmp w3_arb_093c0f64.c -o w3_arb -lflint -lmpfr -lgmp -lm
    gcc -O3 -march=x86-64-v3 -ffp-contract=off -fopenmp w3_arb_inst_d21d8507.c -o w3_arb_inst -lflint -lmpfr -lgmp -lm
    cp w3_arb_093c0f64.c w3_arb.c
    gcc -O3 -march=x86-64-v3 -ffp-contract=off -fopenmp w3_tabletest.c -o w3_tabletest -lflint -lmpfr -lgmp -lm
    gcc -O2 -DWIN=3 -DWCERT=3 -DWAREA=3 mcw3dec.c -o mcw3dec -lm
    gcc -O3 -march=native -fopenmp -frounding-math ../chk/src/chk_w3_ede9de74.c -o chk_w3 -lflint -lm
    cd ../../level0
    gcc -O2 chk_level0.c -o chk_level0 -lflint -lmpfr -lgmp -lm
    gcc -O2 mc_level0.c -o mc_level0 -lm

The window-3 runs used glibc 2.41, gcc 14.2, FLINT 3.1, MPFR 4.2.2 and GMP 6.3.0.

## Checking

    ./chk_ck14 --selftest 3
    ./chk_ck14 3 0.1 0.0002 1e-12 --ninit 4096
    ./chk_ck14 4 0.4 0.0005 1e-13 --ninit 262144 --shard LO HI      # LO = 16384 s, HI = LO + 16384, s = 0..15
    ./chk_ck14 5 0.6 0.00025 1e-13 --ninit 4194304 --shard LO HI    # LO = 16384 s, HI = LO + 16384, s = 0..255
    ./chk_ck14 --combine LOGFILE...

The logs in `logs/` come from these commands with `OMP_NUM_THREADS` equal to the number of threads of the machine. The
run for k = 3 took 5 s and the 16 ranges for k = 4 took 1,115 s in total, on 192 threads. The 256 ranges for k = 5 took
58,050 s in total, on machines with 176, 128 and 96 threads. The files `logs/k*/combined.txt` are the output of `--combine`
over the range logs.

The arguments are `K W0 WF EPS`: the number of points, the largest width of a box that may be scored, the floor `WF`
(a box is split for its loss only if its relevant width exceeds `WF`), and the loss threshold `EPS` for splitting.
`--ninit N` sets the number of initial boxes, rounded up to a power of two, and `./chk_ck14 --count K N` prints this
number. `--shard LO HI` treats only the initial boxes with indices in `[LO, HI)` and prints a `SHARD` line with the
exact integer `floor(10^30 x)` for the lower endpoint `x` of the sum of its leaf bounds. `--combine` adds these
integers, checks that all ranges come from the same parameters and the same build and do not overlap, and reports the
coverage.

The leaves do not depend on the number of threads. They do not depend on `N` either, as long as the initial bisection
splits only boxes wider than `W0`: for k = 3, 4, 5 this means `N <= 8192`, `N <= 262144` and `N <= 2^26`. The search
program uses for `N` the least power of two that is at least 64 times the number of threads, so for k = 3 it stays in
this range on at most 128 threads. The rigorous sums are rounded in an order that depends on the thread schedule, so
the integers in the `SHARD` lines can differ in their last digits between runs. A k = 3 run on 8 threads gave 9 units
more in the 28th digit. Each of these integers is a valid lower bound, and the printed certified values agree.

Every run prints the two output lines of the search program first, then the rigorous results. A result is accepted
when the line `CERTIFIED  C_k >= x` comes from a run over all initial boxes, or from `--combine` over ranges that cover
all initial boxes, and no `NEGATIVE CONTROL` or `WARNING` line appears. The checker prints `floor(10^10 x)/10^10` for
the lower endpoint `x` of the certified quantity. It also compares each rigorous leaf value with the float value of the
search code (`leaves with rigorous < 0.999 float`).

The environment variable `CHK_MUTATE=g+,pref,orderfac,order,noR,class,old3b,flt+,indep,fmaxlo,enl1` runs negative
controls with deliberate errors (see the source). `CHK_PROGRESS=1` prints progress on standard error. `CHK_ALL=1` also
evaluates the leaves of float value 0, and `CHK_NSTRIP_LOG2=n` uses `2^n` strips in the probability bounds instead of 8.
Both leave the results valid, and the logs were produced without them.

## Checking the terms with 6 <= k <= 22

The quoted value comes from the grid `N1 N2 NT = 60 30 144` (60 radial steps on [0, 1], 30 on [1, 2] and 144 angular
steps), the step `2^-3` in `t`, the cut-off `T = 6` and `KMAX = 22`. Its triple tables were built in 16 slices on 16
machines. Each machine then loaded all slices, after checking their SHA-256, and computed the PHI lines for three of the
48 points of the `t`-grid:

    cd large/window3/src
    W3SLICE="s 16" W3SAVE=slice_s.bin ./w3_arb 60 30 144 3 6 22 THREADS              # s = 0, ..., 15
    W3LOAD="slice_0.bin ... slice_15.bin" ./w3_arb 60 30 144 3 6 22 THREADS J0 J1      # PHI lines for J0 <= j <= J1
    ./w3_arb --int 60 30 144 3 6 22 < PHI_LINES                                        # completeness check and t-integral

On a single machine, `./w3_arb N1 N2 NT 3 6 22 THREADS` does all three steps. At the grid (20,10,48) this takes about
nine minutes on 176 threads. `--int` checks that the PHI lines are complete and consistent and computes the integral
over `t`. Its output for the quoted run is `logs/cert60/combined_60_30_144.txt`, which ends with
`sum_{k=6..22} C_k >= 4.2404631563e-03`. The paper quotes this value rounded down to 10 decimals. All slices and PHI
lines of this run come from `w3_arb_093c0f64.c`. `logs/cert60/SLICE_MANIFEST.txt` lists the slices with their hashes and
the hashes found when they were loaded.

`w3_arb_inst_d21d8507.c` is `w3_arb_093c0f64.c` with counters added to its comparisons by `make_inst_4f3a7d46.py`; they
leave its arithmetic unchanged. A rerun of all 960 PHI lines with it, in `logs/cert60/t60inst/`, reproduces them bit
for bit (`PHI_COMPARE.txt`, written by `scripts/phi_compare.py`). `t60inst/INST_SUMMARY.txt` (`scripts/inst_summary.py`)
reports no subnormal or zero product and no subnormal rescaled entry: the smallest product is 2^-137.08, and the smallest
rescaled entry is 2^-101.06 times the largest entry of its step.

`logs/cert40/` and `logs/cert_w3a/` hold runs at the coarser grids (40,20,96), (30,15,72) and (20,10,48) (sources
`a32632cb`, `ed91d98d` and `3e8d8aeb`). Their PHI lines were combined by `w3_arb_093c0f64.c --int` into the files
`combined_*_enclfix.txt`, which give 0.0039174952 at (40,20,96) and 0.0030379534 at (20,10,48), the values that the
paper compares with the second and third programs. `cert40/combined_40_20_96.txt` is an earlier combination with a
smaller upper enclosure factor. `cert_w3a/d_classes.out` and `d_areas.out` come from `w3_arb_7e03aba8.c` with
`W3DIAG=classes` and `W3DIAG=areas`, which replace the edge classes or the area bounds by sampled values; they are not
rigorous.

Negative controls and the table test (`logs/ctl093/`):

    W3CTRL=noA3 ./w3_arb 10 5 24 3 6 14 THREADS        # also W3CTRL=t1, s1, nohalf, and the grid 20 10 48
    ./w3_tabletest 30 15 72 THREADS 3000 2000 SEED

The controls multiply `abar3` by 0.97, decide the edges `{i+1, i-2}` or `{i+1, i-1}` at the centres of the cells, or
drop the factor 1/2. Each raises the value against the unchanged program (`controls.log`). The table test compares
3,000 random pair entries and 3,000 random triple entries with means over 2,000 samples and checks the edges declared
present at 2,000 further samples on the cell boundaries. It finds no bound more than five standard errors on the wrong
side and no violated edge.

The second implementation is described in `large/window3/chk/README.txt`, with its commands and runs. At (40,20,96) it
gives `sum_{k=6..22} C_k >= 3.955730823653845e-03` (`chk/int/int_dt8.out`), at least the value of the first program for
every `k` (`chk/int/int_vs_main_40.txt`).

The weaker bound of Section 5.5:

    cd large/level0
    ./chk_level0 1000 1048576 0.002 12 30    # NR NPHI DT T KMAX: about 2 minutes
    python3 -I level0_arb.py 1000 0.03125 12 30
    ./mc_level0 20000000 7 30                # Monte Carlo reference, not rigorous

The logs are in `large/level0/logs/`. `level0_arb.py` needs python-flint (tested with 0.9.0). In
`large/level0/controls/` the copies `c_*.c` of `chk_level0.c` and `py_*.py` of `level0_arb.py` ran at a reduced
resolution: 200 radial cells and t-step 1/16 for the script, and 200 radial cells, 2^14 angle intervals and t-step 0.01
for the checker. `controls.log` records the results. All of them raise the value except `py_exp_shift.py`, which uses
the exponent `k + 1/2` and lowers it. This error is detected by the disagreement with `chk_level0`.

## Independent checks

We wrote the programs in `independent/` separately from the search program, the checker and the window-3 programs.
They test components of the checker against their own implementations, compare the bounds of sampled leaves with the
integrals over these leaves, and estimate `C_3, ..., C_6` by Monte Carlo integration. `independent/w3ind.c` evaluates
the bound for 6 <= k <= 22 a third time. We wrote it from a specification of the bound, without the sources of
`w3_arb.c` and `chk_w3.c`. It computes its tables with MPFR and runs its recursion with directed rounding. These
programs are checks, not part of the proof. `independent/README.md` gives the commands and the results reported in the
paper.

## Lean proofs

`lean/` is a copy of the Lean release tree, with its own hash list `lean/SHA256SUMS`. It contains no compiled files,
so every module, including every check, is evaluated again when it is built. The toolchain is Lean v4.35.0-rc3 with
Mathlib commit c55e6e786f49 (`lean-toolchain`, `lake-manifest.json`).

- `lean/native_v3/`: `BHH.mainBoundsV3_N : MainBoundsV3`, proved in `BHH/MainN3.lean` and stated in
  `BHH/StatementW3.lean`. `MainBoundsV3` states `C_3 >= 0.0117130195`, `C_4 >= 0.0063707166` and `C_5 >= 0.0035280362`,
  the bounds of the theorem, under `GreenFormula` and `VertexLemmaSeg`. For `C_3` and `C_4` it uses the same 62 and
  1,142 ranges of initial boxes as `lean/native/`, and for `C_5` the subdivision of Table 1 of the paper, with claims on
  4,457 ranges; the other 1,613 ranges, on which the sums of the C program are 0, receive the bound 0. The proof depends
  on `propext`, `Classical.choice`, `Quot.sound` and 5,667 auxiliary axioms of `native_decide`, as `axioms_N3.txt`
  shows: 5,661 for ranges of initial boxes and 6 for checks of the tables of `g`. `BHH/BetaN3.lean` and
  `W3/Assembly.lean` derive `beta >= 0.6508522354`, in the form of `BetaBoundV2` and `BHHBetaBoundV2`, from
  `MainBoundsV3` and a hypothesis `W3Bound`, which says that `GreenFormula` and `VertexLemmaSeg` imply
  `C_6 + ... + C_22 >= 0.0042404631` and is not proved in Lean. Evaluating the 4,457 new ranges, together with the C
  program that computed their claims, took about five hours on up to about 100 machines. `BUILD.md` describes the build.
- `lean/native/`: `BHH.betaBoundV2_N : BetaBoundV2` and `BHH.bhhBetaBoundV2_N : BHHBetaBoundV2`, proved in
  `BHH/BetaN.lean` and stated in `BHH/StatementV2.lean`. `BetaBoundV2` says that every real `beta` with
  `DongCaoK30 beta` satisfies `beta >= 0.6491725104 = 5/8 + 0.0117130195 + 0.0063707166 + 0.0034034701 + 0.0026853042`.
  The bound for `C_5` comes from the subdivision with `EPS = 3e-13` (tol in the paper) and otherwise the values of `W0`,
  `WF` and `N` of Table 1 of the paper, and the last term bounds `C_6 + ... + C_30` with the window of two places
  described in Section 6.2 of the paper. The proof depends on `propext`, `Classical.choice`, `Quot.sound` and 5,536
  auxiliary axioms of `native_decide`, one for each compiled check that it uses, as `axioms_N.txt` shows: 5,520 for
  ranges of initial boxes, 6 for checks of the tables of `g` and 10 for checks of the window-two bound. Evaluating the
  5,520 ranges took about three hours on up to 60 machines with 96 threads each. `BUILD.md` describes the build.
- `lean/kernel/`: `BHH.betaBoundK2 : BetaBoundK2` and `BHH.bhhBetaBoundK2 : BHHBetaBoundK2`, proved in `BHH/MainK2.lean`
  and stated in `BHH/StatementK2.lean`: the same with `beta >= 0.6426496`, from the bounds `C_3 >= 0.0117130195` and
  `C_4 >= 0.0059365909` of `BHH.mainBoundsK2 : MainBoundsK2`. The bound for `C_3` is that of the theorem, on the
  subdivision of the paper's run; the bound for `C_4` comes from a coarser subdivision with 512 initial boxes,
  `W0 = 0.4`, `WF = 0.002` and `EPS = 3e-10`. The bound 0.6426496 is above 5/8 + 0.011135 + 0.005040 + 0.001015 =
  0.64219, the bound given by the values of Dong and Cao for `C_3`, `C_4` and `C_5`. The proof uses only the three
  standard axioms (`AXIOMS_K2.txt`). Its 51,282 generated modules are not shipped: `GEN_PARAMS.txt` gives the two
  commands that regenerate them with `tools/gen_kcut.py` from the cut data `k3_all.txt` and `k4_all.txt`, and
  `KSub2_SHA256SUMS` lists their hashes. The cut data are the files `k3_all.txt.xz` and `k4_all.txt.xz` of the Zenodo
  record, decompressed; `kc2/UNCOMPRESSED_SHA256` gives the SHA-256 of the uncompressed files. Building the generated
  modules, among them the 46,096 modules with the 979,442 theorems on the pieces, took about 5,250 hours of
  single-threaded time in total.

The three hypotheses are defined in `BHH/Defs.lean` and `BHH/DefsV2.lean`. `GreenFormula` is Green's formula (3.1) of
the paper for distinct points. `VertexLemmaSeg` is Lemma 3.1 with Remark 3.2 and the gradient formula (3.2), along the
segment from the expansion point. `DongCaoK30 beta` says `beta >= 5/8 + C_3 + ... + C_30`, from Theorem 3 of Dong and
Cao. The theorems for the BHH constant assume `DongCaoK30 beta` for every `beta` with `IsBHHConstant beta`.

Comments in the Lean files that mention version 2 of the paper refer to doi:10.5281/zenodo.23534689, whose main
theorem was the native bound 0.6491725104. `lean/README.md` explains the lemma and equation numbers in the comments.

## License

Apache License 2.0, see `LICENSE`.

## Citation

See `CITATION.cff`.
