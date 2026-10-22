# Lean 4 proof of the three C_k bounds of Theorem 1.1 (native evaluation by native_decide)

Theorem (`BHH/MainN3.lean`):

    theorem BHH.mainBoundsV3_N : MainBoundsV3   -- C_3 >= 0.0117130195, C_4 >= 0.0063707166, C_5 >= 0.0035280362

The statement is in `BHH/StatementW3.lean`. It is an implication from two named hypotheses. `GreenFormula`, in
`BHH/Defs.lean`, is Green's formula (3.1). `VertexLemmaSeg`, in `BHH/DefsV2.lean`, is Lemma 3.1 with Remark 3.2 and the
gradient formula (3.2), along a segment. `BHH/BetaN3.lean` also proves the assembly lemmas from `MainBoundsV3` and a
window-3 bound `W3BoundAt w` to beta >= 5/8 + C_3 + C_4 + C_5 + w; the window-3 bound is a hypothesis there and is not
proved here.

Axioms (`axioms_N3.txt`, printed by `lean BHH/AxN3.lean`): `propext`, `Classical.choice`, `Quot.sound` and 5,667
auxiliary axioms of `native_decide`; nothing else. Of the auxiliary axioms, 5,661 are for box shards (62 for C_3, 1,142
for C_4 and 4,457 for C_5) and 6 for the g tables.

Build: Lean v4.35.0-rc3 and Mathlib c55e6e786f49 (`lean-toolchain`, `lake-manifest.json`). `lake build` covers the
libraries `BHH` and `BHHCert`; the shard, chain and assembly modules are compiled with plain `lean -o` in the order that
`BUILD.md` gives ("Build route"). `BUILD.md` also describes the files and a full kernel replay. `SHA256SUMS` lists every file of this directory except itself and this README.

Lemma, proposition and remark numbers in the comments of the Lean files are those of the paper. Green's formula and the
gradient formula are cited there as (2.1) and (2.2); they are (3.1) and (3.2) in the paper. Section numbers in the
comments may differ from those of the paper.
