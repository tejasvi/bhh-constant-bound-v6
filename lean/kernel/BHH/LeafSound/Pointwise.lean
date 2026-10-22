/-
Module D, part 9: the vertex lemma on the closed box of a leaf (`A(y)` against its linearization at the centres).
-/
import BHH.LeafSound.Finish

open BHH.Cert Real MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace BHH

/-- points of the closed real box lie in the code's (closed) rectangles -/
lemma mem_boxRects_rbox {k : ℕ} {lo hi : List ℤ} {x : Fin (mDim k) → ℝ}
    (hx : x ∈ rbox (realLo k lo) (realLo k hi)) (hk : 3 ≤ k) (i : Fin k) :
    (boxRects k lo hi i).Mem (xcfg k x i) := by
  have hx' : ∀ d : Fin (mDim k), fx (lo.getD d.val 0) ≤ x d ∧ x d ≤ fx (hi.getD d.val 0) := by
    intro d; have := hx d (Set.mem_univ _); simpa [realLo] using this
  have hm : mDim k = 2 * k - 3 := rfl
  unfold boxRects rectOf Rect.Mem
  rw [ptBoxes_getD]
  unfold xcfg
  by_cases h0 : i.val = 0
  · simp [h0, fx_zero]
  · by_cases h1 : i.val = 1
    · have h0m : 0 < mDim k := by rw [hm]; omega
      have := hx' ⟨0, h0m⟩
      simp only [h0, h1, ite_false, ite_true, listGet]
      rw [xget_of_lt x h0m]
      exact ⟨this.1, this.2, by simp [fx_zero], by simp [fx_zero]⟩
    · have hi := i.isLt
      have ha : 2 * i.val - 3 < mDim k := by rw [hm]; omega
      have hb : 2 * i.val - 2 < mDim k := by rw [hm]; omega
      have h3 := hx' ⟨2 * i.val - 3, ha⟩
      have h4 := hx' ⟨2 * i.val - 2, hb⟩
      simp only [h0, h1, ite_false, listGet]
      rw [xget_of_lt x ha, xget_of_lt x hb]
      exact ⟨h3.1, h3.2, h4.1, h4.2⟩

/-- the centres of the code's rectangles are the configuration of the centre of the box -/
lemma centre_eq_xcfg {k : ℕ} (hk : 3 ≤ k) (lo hi : List ℤ) (i : Fin k) :
    (boxRects k lo hi i).centre = xcfg k (fun d => (realLo k lo d + realLo k hi d) / 2) i := by
  have hm : mDim k = 2 * k - 3 := rfl
  unfold boxRects rectOf Rect.centre
  rw [ptBoxes_getD]
  unfold xcfg
  by_cases h0 : i.val = 0
  · simp [h0, fx_zero]
  · by_cases h1 : i.val = 1
    · have h0m : 0 < mDim k := by rw [hm]; omega
      simp only [h0, h1, ite_false, ite_true, listGet]
      rw [xget_of_lt _ h0m]
      simp [realLo, fx_zero]
    · have hi := i.isLt
      have ha : 2 * i.val - 3 < mDim k := by rw [hm]; omega
      have hb : 2 * i.val - 2 < mDim k := by rw [hm]; omega
      simp only [h0, h1, ite_false, listGet]
      rw [xget_of_lt _ ha, xget_of_lt _ hb]
      simp [realLo]

lemma gap_comm (a b c d : ℝ) : gap a b c d = gap c d a b := by
  unfold gap; rw [max_comm (c - b) (a - d)]

lemma dminSq_comm (R S : Rect) : dminSq R S = dminSq S R := by
  unfold dminSq; rw [gap_comm R.xl, gap_comm R.yl]

lemma thr198_lt : thr198 < 4 * ONE * ONE := by
  unfold thr198 ONE; norm_num

/-- the vertex lemma on the closed box of a leaf, when all pairs have `d⁻ > 0` -/
theorem vertex_bound {k : ℕ} (hk : 3 ≤ k) {lo hi : List ℤ} (hVL : VertexLemmaSeg)
    (hpos : ∀ i j : Fin k, i < j → 0 < dminSq (boxRects k lo hi i) (boxRects k lo hi j))
    {x : Fin (mDim k) → ℝ} (hx : x ∈ rbox (realLo k lo) (realLo k hi)) :
    let R := boxRects k lo hi
    let c : Fin k → Pt := fun i => (R i).centre
    |unionArea (xcfg k x) - unionArea c
        - ∑ i, ((greenGrad c i).1 * (xcfg k x i - c i).1 + (greenGrad c i).2 * (xcfg k x i - c i).2)|
      ≤ vertexRemSeg c (xcfg k x) (fun i => (R i).eps) (fun i j => √(dminSq (R i) (R j)))
          (fun i j => √(dmaxSq (R i) (R j))) (codeFirst k lo hi) := by
  intro R c
  have h := vertexLemma_of_seg hVL k R (codeFirst k lo hi) ?_ ?_ (xcfg k x) (fun i => mem_boxRects_rbox hx hk i)
  · rw [VertexRect.vertexRem_eq] at h; exact h
  · intro i j hij
    rcases lt_or_gt_of_ne hij with h | h
    · exact hpos i j h
    · rw [dminSq_comm]; exact hpos j i h
  · intro i j hf
    have hf' : (d2minmax ((ptBoxes k lo hi).getD i.val default) ((ptBoxes k lo hi).getD j.val default)).2 < thr198 := by
      simpa [codeFirst] using hf
    have hmax := dmaxSq_rectOf ((ptBoxes k lo hi).getD i.val default) ((ptBoxes k lo hi).getD j.val default)
    show dmaxSq (boxRects k lo hi i) (boxRects k lo hi j) < 4
    unfold boxRects; rw [hmax, ← ONE_sq4_cast]
    have := lt_trans hf' thr198_lt
    have : ((d2minmax ((ptBoxes k lo hi).getD i.val default) ((ptBoxes k lo hi).getD j.val default)).2 : ℝ) <
        ((4 * ONE * ONE : ℤ) : ℝ) := by exact_mod_cast this
    gcongr

end BHH
