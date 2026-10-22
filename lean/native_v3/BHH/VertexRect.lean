/-
`VertexLemmaSeg → VertexLemma`: the segment form of the vertex lemma (the hypothesis of the v2 statements) implies
the rectangle form of `BHH/Defs.lean` (the hypothesis that the box proofs use).

For rectangles `R_i` containing `y_i`, the segment from the centres `c_i` to `y_i` stays in the rectangles, so every
pair distance along it lies in `[√dminSq, √dmaxSq]`, and `|y_i - c_i| ≤ ε_i` (half diagonal).  With
`dlo = √dminSq`, `dhi = √dmaxSq` and `ε = Rect.eps`, `vertexRemSeg` is `vertexRem` term by term.
-/
import BHH.DefsV2

open Set Real

namespace BHH

namespace VertexRect

/-- `gap a b c d ≤ |x - y|` for `x ∈ [a, b]`, `y ∈ [c, d]`. -/
lemma gap_le_abs {a b c d x y : ℝ} (hx : a ≤ x ∧ x ≤ b) (hy : c ≤ y ∧ y ≤ d) :
    gap a b c d ≤ |x - y| := by
  unfold gap
  refine max_le (max_le ?_ ?_) (abs_nonneg _)
  · have : c - b ≤ y - x := by linarith [hx.2, hy.1]
    calc c - b ≤ y - x := this
      _ ≤ |x - y| := by rw [abs_sub_comm]; exact le_abs_self _
  · have : a - d ≤ x - y := by linarith [hx.1, hy.2]
    exact this.trans (le_abs_self _)

lemma gap_nonneg (a b c d : ℝ) : 0 ≤ gap a b c d := le_max_right _ _

/-- `|x - y| ≤ span a b c d` for `x ∈ [a, b]`, `y ∈ [c, d]`. -/
lemma abs_le_span {a b c d x y : ℝ} (hx : a ≤ x ∧ x ≤ b) (hy : c ≤ y ∧ y ≤ d) :
    |x - y| ≤ span a b c d := by
  unfold span
  rw [abs_le]
  constructor
  · have : y - x ≤ d - a := by linarith [hx.1, hy.2]
    have h2 : d - a ≤ |d - a| := le_abs_self _
    have h3 : |d - a| ≤ max |d - a| |b - c| := le_max_left _ _
    linarith
  · have : x - y ≤ b - c := by linarith [hx.2, hy.1]
    have h2 : b - c ≤ |b - c| := le_abs_self _
    have h3 : |b - c| ≤ max |d - a| |b - c| := le_max_right _ _
    linarith

lemma dminSq_nonneg (R S : Rect) : 0 ≤ dminSq R S := by unfold dminSq; positivity

lemma dmaxSq_nonneg (R S : Rect) : 0 ≤ dmaxSq R S := by unfold dmaxSq; positivity

/-- For `p ∈ R`, `q ∈ S`: `dminSq R S ≤ sqDist p q ≤ dmaxSq R S`. -/
lemma dminSq_le_sqDist {R S : Rect} {p q : Pt} (hp : R.Mem p) (hq : S.Mem q) :
    dminSq R S ≤ sqDist p q ∧ sqDist p q ≤ dmaxSq R S := by
  obtain ⟨hp1, hp2, hp3, hp4⟩ := hp
  obtain ⟨hq1, hq2, hq3, hq4⟩ := hq
  have g1 := gap_le_abs (a := R.xl) (b := R.xh) (c := S.xl) (d := S.xh) ⟨hp1, hp2⟩ ⟨hq1, hq2⟩
  have g2 := gap_le_abs (a := R.yl) (b := R.yh) (c := S.yl) (d := S.yh) ⟨hp3, hp4⟩ ⟨hq3, hq4⟩
  have s1 := abs_le_span (a := R.xl) (b := R.xh) (c := S.xl) (d := S.xh) ⟨hp1, hp2⟩ ⟨hq1, hq2⟩
  have s2 := abs_le_span (a := R.yl) (b := R.yh) (c := S.yl) (d := S.yh) ⟨hp3, hp4⟩ ⟨hq3, hq4⟩
  have n1 := gap_nonneg R.xl R.xh S.xl S.xh
  have n2 := gap_nonneg R.yl R.yh S.yl S.yh
  unfold dminSq dmaxSq sqDist
  constructor
  · have e1 : gap R.xl R.xh S.xl S.xh ^ 2 ≤ (p.1 - q.1) ^ 2 := by
      rw [← sq_abs (p.1 - q.1)]; exact pow_le_pow_left₀ n1 g1 2
    have e2 : gap R.yl R.yh S.yl S.yh ^ 2 ≤ (p.2 - q.2) ^ 2 := by
      rw [← sq_abs (p.2 - q.2)]; exact pow_le_pow_left₀ n2 g2 2
    linarith
  · have e1 : (p.1 - q.1) ^ 2 ≤ span R.xl R.xh S.xl S.xh ^ 2 := by
      rw [← sq_abs (p.1 - q.1)]; exact pow_le_pow_left₀ (abs_nonneg _) s1 2
    have e2 : (p.2 - q.2) ^ 2 ≤ span R.yl R.yh S.yl S.yh ^ 2 := by
      rw [← sq_abs (p.2 - q.2)]; exact pow_le_pow_left₀ (abs_nonneg _) s2 2
    linarith

/-- The segment from the centre of a rectangle to one of its points stays in the rectangle. -/
lemma segPt_mem {R : Rect} {y : Pt} (hy : R.Mem y) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    R.Mem (segPt R.centre y t) := by
  obtain ⟨h1, h2, h3, h4⟩ := hy
  obtain ⟨t0, t1⟩ := ht
  unfold Rect.Mem segPt Rect.centre
  simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, Prod.fst_sub, Prod.snd_sub,
    smul_eq_mul]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith

/-- `|y - c| ≤ ε` for a point `y` of a rectangle with centre `c` and half diagonal `ε`. -/
lemma enorm2_sub_centre_le {R : Rect} {y : Pt} (hy : R.Mem y) : enorm2 (y - R.centre) ≤ R.eps := by
  obtain ⟨h1, h2, h3, h4⟩ := hy
  unfold enorm2 Rect.eps Rect.centre
  simp only [Prod.fst_sub, Prod.snd_sub]
  rw [show √((R.xh - R.xl) ^ 2 + (R.yh - R.yl) ^ 2) / 2
      = √(((R.xh - R.xl) ^ 2 + (R.yh - R.yl) ^ 2) / 4) by
    rw [Real.sqrt_div' _ (by norm_num : (0:ℝ) ≤ 4)]
    rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)]]
  apply Real.sqrt_le_sqrt
  nlinarith

lemma sqrt_dmaxSq_sq (R S : Rect) : √(dmaxSq R S) ^ 2 = dmaxSq R S :=
  Real.sq_sqrt (dmaxSq_nonneg R S)

/-- `Tbound` is `Tseg` with `dlo = √dminSq`, `dhi = √dmaxSq`. -/
lemma Tbound_eq_Tseg (R S : Rect) (first : Bool) (w : ℝ) :
    Tbound R S first w = Tseg (√(dminSq R S)) (√(dmaxSq R S)) first w := by
  unfold Tbound Tseg
  rw [sqrt_dmaxSq_sq]

lemma certCovered_iff {k : ℕ} (R : Fin k → Rect) (first : Fin k → Fin k → Bool) (i j : Fin k) (P : Pt) :
    certCovered R first i j P ↔
      certCoveredSeg (fun i => (R i).centre) (fun i => (R i).eps) (fun i j => √(dminSq (R i) (R j)))
        (fun i j => √(dmaxSq (R i) (R j))) first i j P := by
  unfold certCovered certCoveredSeg
  simp only [Tbound_eq_Tseg]

lemma nuCount_eq {k : ℕ} (R : Fin k → Rect) (first : Fin k → Fin k → Bool) (i j : Fin k) :
    nuCount R first i j =
      nuCountSeg (fun i => (R i).centre) (fun i => (R i).eps) (fun i j => √(dminSq (R i) (R j)))
        (fun i j => √(dmaxSq (R i) (R j))) first i j := by
  have h1 := certCovered_iff R first i j (vertexPts (R i).centre (R j).centre).1
  have h2 := certCovered_iff R first i j (vertexPts (R i).centre (R j).centre).2
  unfold nuCount nuCountSeg
  split_ifs <;> simp_all

lemma sqrt_lt_two_iff {x : ℝ} : √x < 2 ↔ x < 4 := by
  rw [Real.sqrt_lt' (by norm_num : (0:ℝ) < 2)]; norm_num

lemma vertexRem_eq {k : ℕ} (R : Fin k → Rect) (first : Fin k → Fin k → Bool) (y : Fin k → Pt) :
    vertexRem R first y =
      vertexRemSeg (fun i => (R i).centre) y (fun i => (R i).eps) (fun i j => √(dminSq (R i) (R j)))
        (fun i j => √(dmaxSq (R i) (R j))) first := by
  unfold vertexRem vertexRemSeg
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have hiff : dminSq (R i) (R j) < 4 ↔ √(dminSq (R i) (R j)) < 2 :=
    sqrt_lt_two_iff.symm
  simp only [hiff, nuCount_eq, Tbound_eq_Tseg]

end VertexRect

open VertexRect in
/-- The segment form of the vertex lemma implies the rectangle form. -/
theorem vertexLemma_of_seg : VertexLemmaSeg → VertexLemma := by
  intro H k R first hpos hfirst y hy
  rw [vertexRem_eq]
  apply H k (fun i => (R i).centre) y (fun i => (R i).eps) (fun i j => √(dminSq (R i) (R j)))
    (fun i j => √(dmaxSq (R i) (R j))) first
  · intro i j hij
    exact Real.sqrt_pos.mpr (hpos i j (ne_of_lt hij))
  · intro i j _ t ht
    have hpi := segPt_mem (hy i) ht
    have hpj := segPt_mem (hy j) ht
    obtain ⟨h1, h2⟩ := dminSq_le_sqDist hpi hpj
    unfold edist2
    exact ⟨Real.sqrt_le_sqrt h1, Real.sqrt_le_sqrt h2⟩
  · intro i j _ hf
    exact sqrt_lt_two_iff.mpr (hfirst i j hf)
  · intro i
    exact enorm2_sub_centre_le (hy i)

end BHH
