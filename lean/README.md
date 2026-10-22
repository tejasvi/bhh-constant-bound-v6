# Lean 4 formalization (A lower bound of 0.6508 for the Beardwood-Halton-Hammersley constant)

* `native_v3/`: the bounds C_3 >= 0.0117130195, C_4 >= 0.0063707166 and C_5 >= 0.0035280362 of Theorem 1.1 of the
  paper, with evaluation by `native_decide` (the second native proof).
* `native/`: beta >= 0.6491725104 (the weaker native bound of Section 6 of the paper), with evaluation by
  `native_decide` (the first native proof).
* `kernel/`: beta >= 0.6426496 with kernel evaluation only and the standard axioms (the kernel-only proof); its
  bound for C_3 is that of Theorem 1.1. The cut data from which its generated modules are built are in the Zenodo
  record of the paper's data (`kernel/README.md`).

All three prove implications from named hypotheses: Green's formula and the vertex lemma along a segment, and for the
two bounds for beta also Theorem 3 of Dong and Cao. Each part has its own README. `SHA256SUMS` lists every file of
this directory.

Lemma, proposition and remark numbers in the comments of the Lean files are those of the paper. Green's formula and
the gradient formula are cited there as (2.1) and (2.2); they are (3.1) and (3.2) in the paper. Section numbers in
the comments may differ from those of the paper.

Some comments use internal labels: "track N" and "track K" mean the native proofs and the kernel-only proof, "module
D" the proof of leaf soundness (`BHH/LeafSound`), and "module E" the proof of Lemma 2.2 of the paper and its parts
(the constants kappa_k, the coordinates, the invariances and the tables of g).
