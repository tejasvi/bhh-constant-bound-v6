# Lean 4 proof of beta >= 0.6426496 (kernel only, standard axioms)

Theorems (`BHH/MainK2.lean`):

    theorem BHH.mainBoundsK2   : MainBoundsK2    -- C_3 >= 0.0117130195 and C_4 >= 0.0059365909
    theorem BHH.betaBoundK2    : BetaBoundK2     -- beta >= 0.6426496 for every beta with DongCaoK30 beta
    theorem BHH.bhhBetaBoundK2 : BHHBetaBoundK2  -- the same for the BHH constant

The label K2 in the names (`MainK2`, `MainBoundsK2`, `AXIOMS_K2.txt`, `AxK2.lean`, ...) marks this kernel-only proof.
The statements are in `BHH/StatementK2.lean`. They use the objects and the three named hypotheses of the native proof:
`GreenFormula` (`BHH/Defs.lean`), `VertexLemmaSeg` and `DongCaoK30` (`BHH/DefsV2.lean`). `DongCaoK30 beta` says
beta >= 5/8 + sum_{k=3}^{30} C_k (Theorem 3 of Dong and Cao with K = 30). The theorem for the BHH constant assumes
`DongCaoK30 beta` for every beta with `IsBHHConstant beta`.

The tree of C_3 is the subdivision of the paper's run for k = 3 (W0 0.1, Wf 0.0002, tol 1e-12, 4,096 initial boxes),
so `mainBoundsK2` proves the paper's bound for C_3 by kernel evaluation. The tree of C_4 is coarser (W0 0.4, Wf 0.002,
tol 3e-10, 512 initial boxes).

Axioms (`AXIOMS_K2.txt`, printed by `lake env lean AxK2.lean`): `propext`, `Classical.choice`, `Quot.sound` only.
Every leaf value is computed by the Lean kernel (`decide +kernel`). Some imported modules that the native proof also
uses contain `native_decide` lemmas; the theorems above do not use them, as the axiom list shows.

Files:
- the import closure of `BHH/MainK2.lean` without the generated modules `BHH/KSub2/**` (51,282 files, not shipped),
  and the library root `BHHCert.lean`;
- `AxK2.lean`, which prints the axioms and the statements (its output is `AXIOMS_K2.txt`);
- the untrusted cut generator `BHHCert/KCutGen2.lean` and the module it imports for the tree codes,
  `BHHCert/TreeKGen.lean` (no proof module imports either); `lakefile_kcut2_snippet.toml` declares the executable `kcut2`;
- the untrusted module writer `tools/gen_kcut.py`, with its parameters and commands in `GEN_PARAMS.txt`;
- `KSub2_SHA256SUMS` (sha256 of the 51,282 generated files), and `kc2/RECORDS_SHA256` and `kc2/UNCOMPRESSED_SHA256`
  (sha256 of the cut data, compressed and uncompressed);
- `lakefile.toml`, `lake-manifest.json`, `lean-toolchain`, and `SHA256SUMS` (sha256 of every file except itself and
  this README).

`lakefile.toml` also declares development executables (`bnbfloat`, `exacttest`, `uniontest`, `benchtest`,
`bnbdriver`, `treedriver`, `leafdump`, `profile`) whose sources are not included; neither the proof nor the generator
uses them.

Cut data: the two files k3_all.txt and k4_all.txt are published with the paper's data, compressed, as `k3_all.txt.xz`
and `k4_all.txt.xz` (sha256 of the .xz files in `kc2/RECORDS_SHA256`, of the uncompressed files in
`kc2/UNCOMPRESSED_SHA256`). To regenerate `BHH/KSub2`, put the two .xz files into `kc2/`; then, from this directory,
run `(cd kc2 && sha256sum -c RECORDS_SHA256 && xz -dk k3_all.txt.xz k4_all.txt.xz && sha256sum -c UNCOMPRESSED_SHA256)`,
the two commands in `GEN_PARAMS.txt`, and `sha256sum -c KSub2_SHA256SUMS`. The 46,096 chunk modules hold 979,442
theorems `subOK k (LkKf k) chunk = true` (645,003 for C_3 and 334,439 for C_4), each proved by `decide +kernel` with at
most 25 leaves (17,534,130 leaves in all: 11,563,336 for C_3 and 5,970,794 for C_4). Each of the 2,592 `Data` modules
holds one more theorem `top : cutOK ...`, also proved by `decide +kernel`, which checks the top part of the cut tree of
its box against the claims of its pieces. To rerun the generator itself, append `lakefile_kcut2_snippet.toml` to
`lakefile.toml` and follow step 1 of `GEN_PARAMS.txt`.

Build: Lean v4.35.0-rc3 and Mathlib c55e6e786f49 (`lean-toolchain`, `lake-manifest.json`). After regenerating
`BHH/KSub2`, run `lake build BHH.MainK2`, then `lake env lean AxK2.lean`. The chunk modules do not depend on each other
and can be built in parallel.
