/-
Module D, part 15: the real data of the main branch (all pairs with `d⁻ > 0`): the union area and its gradient at the
centres, the vertex remainder and its bounds, `A(y)` between the code's bounds on the box.
-/
import BHH.LeafSound.BracketGlue
import BHH.LeafSound.DomGlue
import BHH.LeafSound.UnionGlue
import BHH.LeafSound.RemSum

open BHH.Cert Real MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace BHH

lemma boxOf_ae_eq_rbox' {k : ℕ} (lo hi : List ℤ) :
    (boxOf lo hi : Set (Fin (mDim k) → ℝ)) =ᵐ[volume] rbox (realLo k lo) (realLo k hi) := by
  have e1 : (boxOf lo hi : Set (Fin (mDim k) → ℝ)) = Set.pi univ fun d => Ico (realLo k lo d) (realLo k hi d) := rfl
  rw [e1, rbox, volume_pi, Set.pi_univ_Icc]
  exact Measure.univ_pi_Ico_ae_eq_Icc

lemma setLIntegral_boxOf' {k : ℕ} (lo hi : List ℤ) (f : (Fin (mDim k) → ℝ) → ℝ≥0∞) :
    ∫⁻ x in (boxOf lo hi : Set (Fin (mDim k) → ℝ)), f x = ∫⁻ x in rbox (realLo k lo) (realLo k hi), f x :=
  setLIntegral_congr (boxOf_ae_eq_rbox' lo hi)

lemma boxOf_subset_rbox {k : ℕ} (lo hi : List ℤ) :
    (boxOf lo hi : Set (Fin (mDim k) → ℝ)) ⊆ rbox (realLo k lo) (realLo k hi) := by
  intro x hx d _
  have := hx d (Set.mem_univ _)
  exact ⟨this.1, this.2.le⟩

lemma d2minmax_fst_nonneg (P Q : PtBox) : 0 ≤ (d2minmax P Q).1 := by
  unfold d2minmax; simp only; exact add_nonneg (mul_self_nonneg _) (mul_self_nonneg _)

/-- no pair with `d⁻ = 0` in the code: all pairs have `d⁻ > 0` -/
lemma dminSq_pos_of_no3e {k : ℕ} {lo hi : List ℤ}
    (h : ¬((List.map (fun x => d2minmax ((ptBoxes k lo hi).getD x.1 default) ((ptBoxes k lo hi).getD x.2 default))
          (pairList k)).any fun x => x.1 == 0) = true)
    (i j : Fin k) (hij : i < j) : 0 < dminSq (boxRects k lo hi i) (boxRects k lo hi j) := by
  have hmem : (i.val, j.val) ∈ pairList k := mem_pairList.mpr ⟨hij, j.isLt⟩
  have hne : (d2minmax ((ptBoxes k lo hi).getD i.val default) ((ptBoxes k lo hi).getD j.val default)).1 ≠ 0 := by
    intro h0; apply h
    rw [List.any_eq_true]
    exact ⟨_, List.mem_map.mpr ⟨(i.val, j.val), hmem, rfl⟩, by simp only [h0, beq_self_eq_true]⟩
  have h0 := d2minmax_fst_nonneg ((ptBoxes k lo hi).getD i.val default) ((ptBoxes k lo hi).getD j.val default)
  have hpos : (0 : ℝ) < (d2minmax ((ptBoxes k lo hi).getD i.val default)
      ((ptBoxes k lo hi).getD j.val default)).1 := by exact_mod_cast lt_of_le_of_ne h0 (Ne.symm hne)
  unfold boxRects; rw [dminSq_rectOf]; positivity

/-- the vertex remainder at `x`: `|A(y) - A(c) - ⟨∇A(c), x - c⟩| ≤ ρ(x)`, `0 ≤ ρ(x) ≤ R_max` -/
theorem area_lin_bounds {k : ℕ} (hk3 : 3 ≤ k) (hk5 : k ≤ 5) {lo hi : List ℤ} (hv : ValidBox k lo hi)
    (hVL : VertexLemmaSeg) (hRM : RemMaxProp) (hRMo : RemMomentsProp)
    {cs : ℤ → Iv × Iv} (hcs : CosSinSound cs) (asinC : AsinFn) {rr : RemRes}
    (hrr : remainder cs asinC (ptBoxes k lo hi) (pairList k)
      ((pairList k).map fun (i, j) => d2minmax ((ptBoxes k lo hi).getD i default) ((ptBoxes k lo hi).getD j default))
      = some rr)
    (hpos : ∀ i j : Fin k, i < j → 0 < dminSq (boxRects k lo hi i) (boxRects k lo hi j))
    {x : Fin (mDim k) → ℝ} (hx : x ∈ rbox (realLo k lo) (realLo k hi)) :
    let R := boxRects k lo hi
    let c : Fin k → Pt := fun i => (R i).centre
    let ρ := vertexRemSeg c (xcfg k x) (fun i => (R i).eps) (fun i j => √(dminSq (R i) (R j)))
      (fun i j => √(dmaxSq (R i) (R j))) (codeFirst k lo hi)
    let lin := ∑ d, gradBox k (greenGrad c) d * (x d - (realLo k lo d + realLo k hi d) / 2)
    |unionArea (xcfg k x) - unionArea c - lin| ≤ ρ ∧ 0 ≤ ρ ∧ ρ ≤ fx rr.Rmax := by
  intro R c ρ lin
  have hcx : c = xcfg k (fun d => (realLo k lo d + realLo k hi d) / 2) :=
    funext (fun i => centre_eq_xcfg hk3 lo hi i)
  have hdd : ∀ i j : Fin k, i < j → √(dminSq (R i) (R j)) < 2 →
      0 < √(dminSq (R i) (R j)) ∧ √(dminSq (R i) (R j)) ≤ √(dmaxSq (R i) (R j)) := by
    intro i j hij _
    exact ⟨Real.sqrt_pos.mpr (hpos i j hij), Real.sqrt_le_sqrt (dminSq_le_dmaxSq_box hk3 hv i j)⟩
  have heps : ∀ i, enorm2 (xcfg k x i - c i) ≤ (R i).eps :=
    fun i => VertexRect.enorm2_sub_centre_le (mem_boxRects_rbox hx hk3 i)
  refine ⟨?_, ?_, ?_⟩
  · have hVB := vertex_bound hk3 hVL hpos hx
    have hgi := grad_identity hk3 hk5 (greenGrad c) x (fun d => (realLo k lo d + realLo k hi d) / 2)
    have hsum : ∑ i, ((greenGrad c i).1 * (xcfg k x i - c i).1 + (greenGrad c i).2 * (xcfg k x i - c i).2) = lin := by
      show _ = ∑ d, gradBox k (greenGrad c) d * (x d - (realLo k lo d + realLo k hi d) / 2)
      rw [← hgi]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [show c i = xcfg k (fun d => (realLo k lo d + realLo k hi d) / 2) i from centre_eq_xcfg hk3 lo hi i]
    simp only at hVB
    rw [hsum] at hVB
    exact hVB
  · have h := (hRMo k (realLo k lo) (realLo k hi) (fun i => (R i).eps) (fun i j => √(dminSq (R i) (R j)))
      (fun i j => √(dmaxSq (R i) (R j))) (codeFirst k lo hi) (realLo_lt hv) hdd).2.1 x
    simp only at h
    rw [← hcx] at h
    exact h
  · have h1 := hRM k c (xcfg k x) (fun i => (R i).eps) (fun i j => √(dminSq (R i) (R j)))
      (fun i j => √(dmaxSq (R i) (R j))) (codeFirst k lo hi) hdd heps
    have h2 := (remainder_sound hk3 hv hcs asinC hrr).1
    exact le_trans h1 h2

end BHH
