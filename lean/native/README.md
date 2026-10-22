# Lean 4 proof of beta >= 0.6491725104 (native evaluation by native_decide)

Theorems (`BHH/BetaN.lean`):

    theorem BHH.betaBoundV2_N    : BetaBoundV2      -- beta >= 0.6491725104 for every beta with DongCaoK30 beta
    theorem BHH.bhhBetaBoundV2_N : BHHBetaBoundV2   -- the same for the BHH constant

from `BHH.mainBoundsV2_N : MainBoundsV2`, the bounds for C_3, C_4 and C_5 in `BHH/MainN.lean`, and
`BHH.W2.w2_bound : W2Bound`, the bound for the sum of C_k for 6 <= k <= 30 in `W2/Final.lean`. The suffix `_N` in these
names and in `axioms_N.txt` marks the native proof. The statements are in `BHH/StatementV2.lean`. They are implications
from three named hypotheses. `GreenFormula`, in `BHH/Defs.lean`, is Green's formula (3.1). `VertexLemmaSeg`, in
`BHH/DefsV2.lean`, is Lemma 3.1 with Remark 3.2 and the gradient formula (3.2), along a segment. `DongCaoK30 beta`, also
in `BHH/DefsV2.lean`, is Theorem 3 of Dong and Cao with K = 30, i.e. beta >= 5/8 + sum_{k=3}^{30} C_k. The theorem for
the BHH constant assumes `DongCaoK30 beta` for every beta with `IsBHHConstant beta`. The sanity statement
`BHH.E.cFinite : CFinite` (every C_k is finite) is also proved.

Axioms (`axioms_N.txt`, printed by `lean BHH/AxN.lean`): `propext`, `Classical.choice`, `Quot.sound` and 5,536 auxiliary
axioms of `native_decide`; nothing else. Of the auxiliary axioms, 5,520 are for box shards, 6 for the g tables and 10
for the window-2 bound. `cFinite` uses the standard three only.

Build: Lean v4.35.0-rc3 and Mathlib c55e6e786f49 (`lean-toolchain`, `lake-manifest.json`). `BUILD.md` lists the
files and describes the build (shards, chains, assembly, the window-2 part with `w2_build/`) and a full kernel replay.
`tools/` holds the shard planner, the chain generator, the closure and olean checks, and the C program that produced
the shard claims (the claims are lower bounds only; Lean re-evaluates every one). `SHA256SUMS` in this directory is
the hash list that `BUILD.md` refers to (every file here except itself and this README).
