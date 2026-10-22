# Native proof: final assembly

`BHH/BetaN.lean`:

    theorem BHH.betaBoundV2_N : BetaBoundV2 := betaBoundV2_of mainBoundsV2_N W2.w2_bound
    theorem BHH.bhhBetaBoundV2_N : BHHBetaBoundV2 := bhhBetaBoundV2_of betaBoundV2_N

with `BHH.mainBoundsV2_N : MainBoundsV2` (`BHH/MainN.lean`) and `BHH.W2.w2_bound : W2Bound` (`W2/Final.lean`).
The statements are in `BHH/StatementV2.lean`.

## Axioms

`axioms_N.txt` is the output of `lean BHH/AxN.lean`. Both theorems depend on `propext`, `Classical.choice`,
`Quot.sound` and 5,536 `native_decide` auxiliary axioms, nothing else:

* `BHH.Shards.k3_s*`, `k4_s*`, `k5_s*` (`._native.native_decide.ax_1_1`): 5,520 shards (62 + 1,142 + 4,316);
* `BHH.gtN_nonneg_D3/D4/D5`, `BHH.E.gtN_check_three/four/five`: the g tables;
* `W2C.prod.shard00` ... `shard07`, `W2C.prod.tint`, `W2C.prod.nondeg`: the window-2 bound.

`BHH.E.cFinite : CFinite` (sanity statement) uses the standard three axioms only.

## Files

`SHA256SUMS` lists every file. The `.lean` files are the import closure of `BHH/AxN.lean` (5,739 files:
BHH 72, BHHCert 10, BHHShard 5,580, W2 60, W2Cert 6, W2Prod 11; the only external import is `Mathlib`) plus the root
`BHHCert.lean` of the precompiled library `BHHCert` and the one module it adds, `BHHCert/CandK.lean` (Lake builds the
library's native code from that root; the shards evaluated it).  The comments and docstrings of some
files were edited after the build (internal labels removed); compiling those modules again gives the same
declarations.
`lakefile.toml`, `lake-manifest.json`, `lean-toolchain`: Lean v4.35.0-rc3, Mathlib c55e6e786f49.
`w2_build/`: the lakefile, manifest and toolchain the W2 modules were built with, and the two library roots it needs.
`tools/`: the shard planner, the chain generator, the closure and olean checks, and the C checker used for the claims.

## Build

1. Shards `BHHShard/K{k}/S*.lean`: `theorem k{k}_sNNNNN : (v : Int) ≤ BHH.Cert.shardNPar k pd a b := by native_decide`
   (k = 4, 5; pd = 8, and 12 for three single-box shards) or `(v : Int) ≤ BHH.Cert.shardN 3 a b := by native_decide`
   (k = 3), one per range [a, b) of initial boxes. The claim v is floor(Σ main sums of the boxes × (1 − 10⁻⁹)) − 1
   in units of 2⁻²⁵⁶, from a first pass of the C checker (`tools/chk_box.c`, per-box sums). The shards were compiled
   with `lean -o` against this tree, with the native library of `BHHCert` (precompileModules) loaded, on 96-vCPU cloud VMs.
2. Chains `BHHShard/K{k}/G*.lean` and `All.lean`: consecutive shards summed with `BHH.shardN_add_le`
   (`BHH/ShardChain.lean`; `shardNPar` shards through `BHH.shardNPar_eq`). The results are
   `k3_all`, `k4_all`, `k5_all : (S_k : Int) ≤ shardN k 0 (2 ^ RN k)`. The types force the box ranges to be contiguous.
3. `BHH/MainN.lean`: `mainBoundsV2_of leafSound_N_final k3_all k4_all k5_all` with the three numeric checks (`norm_num`).
4. `W2/`, `W2Cert/`, `W2Prod/`, `BHH/TwoDisk.lean`: the window-two modules. They were built from the same sources
   with `lake build W2.Final W2Prod.AxFinal` and the two library roots in `w2_build/`; `w2_build/W2Cert.lean` leaves
   out `import W2Cert.ParTest`, an unused test module, so the native library that evaluated the W2 checks did not
   contain it. The resulting `W2Prod/S00`-`S07` and `Nondeg`
   `.olean` files have the same constants as those of the reference W2 build (`tools/OleanCmp.lean`), and
   `BHH.W2.w2_bound` printed the same axioms.
   The 18 BHH/BHHCert modules the W2 build shares with this tree have identical sources. Their `.olean` files from the
   two builds differ only in the recorded package name and in absolute source paths (linter data), and they contain
   identical constants (`tools/OleanCmp.lean`: names, kinds, universe parameters, types, values, inductive data).
5. `BHH/BetaN.lean` and `BHH/AxN.lean` were compiled with `lean` against the `.olean` files of steps 1-4.

## Kernel replay

`tools/ReplayMods.lean` (`Lean.Kernel.Environment.replay`, as in lean4checker) imports `Mathlib` and sends every constant
of the 5,738 modules of the closure (all but `BHH.AxN`) to the kernel again: 16,090 constants were checked and none
was rejected or missing. Skipped by `replay` (unsafe compiler auxiliaries): 24 `*._unsafe_rec` constants.

Times: Lean shards about 3 hours on up to 60 96-vCPU VMs; chains 1.5 min; MainN 8 s; W2 shards 59-72 min wall
(8 at once on one VM); BetaN 10 s; axioms 9 s; replay 34 s.
