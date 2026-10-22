/-
Module D, part 16: the integrand `r_2 φ(A(y))` on the box between the code's `fmin` and `fmax`.
-/
import BHH.LeafSound.MainData

open BHH.Cert Real MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace BHH

/-- the integrand of the box part without the graph factor: `r_2 φ(A(y))`, `φ(t) = t^{-(k - 1/2)}` -/
def leafF (k : ℕ) (x : Fin (mDim k) → ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (xget x 0 * unionArea (xcfg k x) ^ (-((k : ℝ) - 1 / 2)))

lemma F2_ge (k : ℕ) (x : Fin (mDim k) → ℝ) :
    ENNReal.ofReal (2 * dcG (unitGraph (xcfg k x))) * leafF k x ≤ F2 k x := by
  unfold leafF F2
  by_cases hg : 0 ≤ 2 * dcG (unitGraph (xcfg k x))
  · rw [← ENNReal.ofReal_mul hg]; apply le_of_eq; congr 1; ring
  · push_neg at hg
    rw [ENNReal.ofReal_of_nonpos hg.le, zero_mul]; exact zero_le

/-- the union data at the centres from module B -/
lemma union_data {k : ℕ} (hk3 : 3 ≤ k) {lo hi : List ℤ} (hv : ValidBox k lo hi) (hG : GreenFormula)
    (hUS : UnionSoundProp) {cs : ℤ → Iv × Iv} (hcs : CosSinSound cs) (cand : CandFn) {u : UnionRes}
    (hu : BHH.Cert.unionArea cs ((ptBoxes k lo hi).map fun P => (P.xc, P.yc)) ONE cand = some u) :
    ivMem (unionArea (fun i => (boxRects k lo hi i).centre)) u.A ∧
    ∀ i : Fin k, ivMem (greenGrad (fun i => (boxRects k lo hi i).centre) i).1 (u.gx.getD i.val default) ∧
      ivMem (greenGrad (fun i => (boxRects k lo hi i).centre) i).2 (u.gy.getD i.val default) := by
  have h := hUS hG cs hcs cand k (ctrList k lo hi) u (ctrList_length k lo hi) hu
  have e : ptsCfg k (ctrList k lo hi) = fun i => (boxRects k lo hi i).centre :=
    funext (fun i => ptsCfg_ctrList hk3 hv i)
  rw [e] at h
  exact h

/-- the linear term is bounded by the code's `sumb` on the closed box -/
lemma lin_abs_le {k : ℕ} (hk3 : 3 ≤ k) {lo hi : List ℤ} {g : Fin k → Pt} {u : UnionRes}
    (hg : ∀ i : Fin k, ivMem (g i).1 (u.gx.getD i.val default) ∧ ivMem (g i).2 (u.gy.getD i.val default))
    {x : Fin (mDim k) → ℝ} (hx : x ∈ rbox (realLo k lo) (realLo k hi)) :
    |∑ d, gradBox k g d * (x d - (realLo k lo d + realLo k hi d) / 2)| ≤
      fx (sumAbs (gradList k u) (widthList k lo hi)) := by
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) (le_trans ?_ (sumAbs_ge hk3 hg lo hi))
  refine Finset.sum_le_sum (fun d _ => ?_)
  have hxd := hx d (Set.mem_univ _)
  rw [abs_mul]
  have : |x d - (realLo k lo d + realLo k hi d) / 2| ≤ (realLo k hi d - realLo k lo d) / 2 := by
    rw [abs_le]; constructor <;> linarith [hxd.1, hxd.2]
  calc |gradBox k g d| * |x d - (realLo k lo d + realLo k hi d) / 2|
      ≤ |gradBox k g d| * ((realLo k hi d - realLo k lo d) / 2) := mul_le_mul_of_nonneg_left this (abs_nonneg _)
    _ = |gradBox k g d| * (realLo k hi d - realLo k lo d) / 2 := by ring

lemma fx_shrD_mul_le (a b : ℤ) : fx (shrD (a * b) PR) ≤ fx a * fx b := by
  have h := shrD_le (a * b) PR
  unfold fx
  calc ((shrD (a * b) PR : ℤ) : ℝ) / 2 ^ PR ≤ ((a * b : ℤ) : ℝ) / 2 ^ PR / 2 ^ PR := by gcongr
    _ = (a : ℝ) / 2 ^ PR * ((b : ℝ) / 2 ^ PR) := by push_cast; ring

/-- `fmin ≤ r_2 φ(A(y)) ≤ fmax` on the box, and `0 ≤ fmin`, `0 ≤ fmax` -/
theorem leafF_bounds {k : ℕ} (hk3 : 3 ≤ k) (hk5 : k ≤ 5) {lo hi : List ℤ} (hv : ValidBox k lo hi)
    (hG : GreenFormula) (hUS : UnionSoundProp) (hVL : VertexLemmaSeg) (hRM : RemMaxProp)
    (hRMo : RemMomentsProp) (hPi : UnionAreaGePiProp)
    {cs : ℤ → Iv × Iv} (hcs : CosSinSound cs) (cand : CandFn) (asinC : AsinFn) {u : UnionRes} {rr : RemRes}
    (hu : BHH.Cert.unionArea cs ((ptBoxes k lo hi).map fun P => (P.xc, P.yc)) ONE cand = some u)
    (hrr : remainder cs asinC (ptBoxes k lo hi) (pairList k)
      ((pairList k).map fun (i, j) => d2minmax ((ptBoxes k lo hi).getD i default) ((ptBoxes k lo hi).getD j default))
      = some rr)
    (hpos : ∀ i j : Fin k, i < j → 0 < dminSq (boxRects k lo hi i) (boxRects k lo hi j))
    (hlo0 : 0 ≤ listGet lo 0) {fLowA f1 f2 : Iv}
    (hlowA : phiAt k (max piLo (u.A.lo - sumAbs (gradList k u) (widthList k lo hi) - rr.Rmax)) = some (fLowA, f1, f2)) :
    (∀ x ∈ (boxOf lo hi : Set (Fin (mDim k) → ℝ)),
      ENNReal.ofReal (fx (fminOf k (u.A.hi + sumAbs (gradList k u) (widthList k lo hi) + rr.Rmax) (listGet lo 0)))
        ≤ leafF k x ∧
      leafF k x ≤ ENNReal.ofReal (fx (shrU (fLowA.hi * listGet hi 0) PR))) ∧
    0 ≤ fminOf k (u.A.hi + sumAbs (gradList k u) (widthList k lo hi) + rr.Rmax) (listGet lo 0) ∧
    0 ≤ shrU (fLowA.hi * listGet hi 0) PR := by
  obtain ⟨hA, hg⟩ := union_data hk3 hv hG hUS hcs cand hu
  have hk1 : 1 ≤ k := by omega
  have hm : mDim k = 2 * k - 3 := rfl
  have h0m : 0 < mDim k := by rw [hm]; omega
  set sumb := sumAbs (gradList k u) (widthList k lo hi) with hsumb
  set sR : ℝ := (k : ℝ) - 1 / 2 with hsR
  have hs : 0 < sR := by
    have : (3 : ℝ) ≤ k := by exact_mod_cast hk3
    rw [hsR]; linarith
  obtain ⟨hlpos, hlI, -, -⟩ := phiAt_sound k hk1 _ _ _ _ hlowA
  have hfLow0 : 0 ≤ fx fLowA.hi := le_trans (by positivity) (ivMem_hi_le hlI)
  have hhi0 : 0 ≤ fx (listGet hi 0) := by
    have := (hv.2.2.1 0 h0m).1
    exact fx_nonneg_iff.mpr (by unfold listGet at hlo0 ⊢; omega)
  have hfmax0 : 0 ≤ fx (shrU (fLowA.hi * listGet hi 0) PR) :=
    le_trans (mul_nonneg hfLow0 hhi0) (fx_mul_le_shrU _ _)
  refine ⟨?_, ?_, fx_nonneg_iff.mp hfmax0⟩
  · intro x hx
    have hxr := boxOf_subset_rbox lo hi hx
    obtain ⟨hlin, hρ0, hρR⟩ := area_lin_bounds hk3 hk5 hv hVL hRM hRMo hcs asinC hrr hpos hxr
    have hl := lin_abs_le hk3 hg hxr
    set Ay := unionArea (xcfg k x) with hAy
    have hπ : π ≤ Ay := hPi k (xcfg k x) (by omega)
    have hAypos : 0 < Ay := lt_of_lt_of_le Real.pi_pos hπ
    have hAhi := ivMem_hi_le hA
    have hAlo := ivMem_lo_le hA
    rw [abs_le] at hlin hl
    have hup : Ay ≤ fx (u.A.hi + sumb + rr.Rmax) := by
      unfold fx at hAhi ⊢; push_cast
      have : fx sumb = (sumb : ℝ) / 2 ^ PR := rfl
      have h2 : fx rr.Rmax = (rr.Rmax : ℝ) / 2 ^ PR := rfl
      rw [this] at hl; rw [h2] at hρR
      rw [add_div, add_div]; linarith [hlin.2, hl.2]
    have hlow : fx (max piLo (u.A.lo - sumb - rr.Rmax)) ≤ Ay := by
      rw [fx_max]
      refine max_le (le_trans piLo_le hπ) ?_
      unfold fx at hAlo ⊢; push_cast
      have : fx sumb = (sumb : ℝ) / 2 ^ PR := rfl
      have h2 : fx rr.Rmax = (rr.Rmax : ℝ) / 2 ^ PR := rfl
      rw [this] at hl; rw [h2] at hρR
      rw [sub_div, sub_div]; linarith [hlin.1, hl.1]
    -- r_2
    have hx0 := (mem_boxOf_iff.mp hx) ⟨0, h0m⟩
    have hr2 : xget x 0 = x ⟨0, h0m⟩ := xget_of_lt x h0m
    have hr2lo : fx (listGet lo 0) ≤ xget x 0 := by rw [hr2]; exact hx0.1
    have hr2hi : xget x 0 ≤ fx (listGet hi 0) := by rw [hr2]; exact hx0.2.le
    have hr20 : 0 ≤ xget x 0 := le_trans (fx_nonneg_iff.mpr hlo0) hr2lo
    have hphi0 : 0 ≤ Ay ^ (-sR) := Real.rpow_nonneg hAypos.le _
    constructor
    · unfold fminOf
      split
      · rename_i f0 g1 g2 hphi
        obtain ⟨hupos, hfI, -, -⟩ := phiAt_sound k hk1 _ _ _ _ hphi
        unfold leafF
        apply ENNReal.ofReal_le_ofReal
        rw [fx_max, fx_zero]
        by_cases hc : fx (shrD (f0.lo * listGet lo 0) PR) ≤ 0
        · rw [max_eq_right hc]; exact mul_nonneg hr20 hphi0
        · push_neg at hc
          rw [max_eq_left hc.le]
          have h1 := fx_shrD_mul_le f0.lo (listGet lo 0)
          have hf0 : fx f0.lo ≤ Ay ^ (-sR) :=
            le_trans (ivMem_lo_le hfI) (Real.rpow_le_rpow_of_nonpos hAypos hup (by linarith))
          have hlo0' : 0 ≤ fx (listGet lo 0) := fx_nonneg_iff.mpr hlo0
          have hf0pos : 0 ≤ fx f0.lo := by
            by_contra hneg; push_neg at hneg
            have : fx f0.lo * fx (listGet lo 0) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hneg.le hlo0'
            linarith
          calc fx (shrD (f0.lo * listGet lo 0) PR) ≤ fx f0.lo * fx (listGet lo 0) := h1
            _ ≤ Ay ^ (-sR) * xget x 0 := mul_le_mul hf0 hr2lo hlo0' hphi0
            _ = xget x 0 * Ay ^ (-((k : ℝ) - 1 / 2)) := by rw [hsR]; ring
      · simp [fx_zero]
    · unfold leafF
      apply ENNReal.ofReal_le_ofReal
      have hphiA : Ay ^ (-sR) ≤ fx fLowA.hi :=
        le_trans (Real.rpow_le_rpow_of_nonpos hlpos hlow (by linarith)) (ivMem_hi_le hlI)
      calc xget x 0 * Ay ^ (-((k : ℝ) - 1 / 2)) ≤ fx (listGet hi 0) * fx fLowA.hi :=
            mul_le_mul hr2hi hphiA hphi0 hhi0
        _ = fx fLowA.hi * fx (listGet hi 0) := by ring
        _ ≤ _ := fx_mul_le_shrU _ _
  · unfold fminOf
    split
    · exact le_max_right _ _
    · exact le_refl 0

lemma bracketVal_nonneg (k : ℕ) (bv : List Iv) (hw : List ℤ) (A : Iv) (sumb Sb : ℤ) (rr : RemRes) (lo0 hi0 : ℤ) :
    0 ≤ bracketVal k bv hw A sumb Sb rr lo0 hi0 := by
  unfold bracketVal
  dsimp only
  split
  · split_ifs
    · exact le_max_right _ _
    · exact le_refl 0
  · exact le_refl 0

/-- the bracket of module C applied to the leaf: `∫_box r_2 φ(A) ≥ vol · val` -/
theorem bracket_input {k : ℕ} (hk3 : 3 ≤ k) (hk5 : k ≤ 5) {lo hi : List ℤ} (hv : ValidBox k lo hi)
    (hG : GreenFormula) (hUS : UnionSoundProp) (hVL : VertexLemmaSeg) (hRM : RemMaxProp)
    (hRMo : RemMomentsProp) (hPi : UnionAreaGePiProp) (hB : BracketProp)
    {cs : ℤ → Iv × Iv} (hcs : CosSinSound cs) (cand : CandFn) (asinC : AsinFn) {u : UnionRes} {rr : RemRes}
    (hu : BHH.Cert.unionArea cs ((ptBoxes k lo hi).map fun P => (P.xc, P.yc)) ONE cand = some u)
    (hrr : remainder cs asinC (ptBoxes k lo hi) (pairList k)
      ((pairList k).map fun (i, j) => d2minmax ((ptBoxes k lo hi).getD i default) ((ptBoxes k lo hi).getD j default))
      = some rr)
    (hpos : ∀ i j : Fin k, i < j → 0 < dminSq (boxRects k lo hi i) (boxRects k lo hi j))
    (hlo0 : 0 ≤ listGet lo 0) :
    ENNReal.ofReal ((volume (boxOf lo hi : Set (Fin (mDim k) → ℝ))).toReal *
        fx (bracketVal k (gradList k u) (widthList k lo hi) u.A (sumAbs (gradList k u) (widthList k lo hi))
          (sumSq (gradList k u) (widthList k lo hi)) rr (listGet lo 0) (listGet hi 0))) ≤
      ∫⁻ x in boxOf lo hi, leafF k x := by
  obtain ⟨hA, hg⟩ := union_data hk3 hv hG hUS hcs cand hu
  have hm : mDim k = 2 * k - 3 := rfl
  have h0m : 0 < mDim k := by rw [hm]; omega
  set R := boxRects k lo hi with hR
  set c : Fin k → Pt := fun i => (R i).centre with hc
  have hcx : c = xcfg k (fun d => (realLo k lo d + realLo k hi d) / 2) :=
    funext (fun i => centre_eq_xcfg hk3 lo hi i)
  have hdd : ∀ i j : Fin k, i < j → √(dminSq (R i) (R j)) < 2 →
      0 < √(dminSq (R i) (R j)) ∧ √(dminSq (R i) (R j)) ≤ √(dmaxSq (R i) (R j)) := by
    intro i j hij _
    exact ⟨Real.sqrt_pos.mpr (hpos i j hij), Real.sqrt_le_sqrt (dminSq_le_dmaxSq_box hk3 hv i j)⟩
  have hMo := hRMo k (realLo k lo) (realLo k hi) (fun i => (R i).eps) (fun i j => √(dminSq (R i) (R j)))
    (fun i j => √(dmaxSq (R i) (R j))) (codeFirst k lo hi) (realLo_lt hv) hdd
  simp only at hMo
  rw [← hcx] at hMo
  obtain ⟨hρm, hρ0, hρ1, hρ2⟩ := hMo
  obtain ⟨hs1, hs2, hs3⟩ := remainder_sound hk3 hv hcs asinC hrr
  simp only at hs1 hs2 hs3
  have hvol0 : 0 ≤ (volume (rbox (realLo k lo) (realLo k hi))).toReal := ENNReal.toReal_nonneg
  rw [setLIntegral_boxOf']
  refine bracket_glue hk3 (bracketPropK_of hB hk3 hk5) hv hlo0 hA hg hρm ?_ ?_ ?_ ?_
  · refine ⟨fx rr.Rmax, fun x hx => ⟨hρ0 x, ?_⟩⟩
    exact (area_lin_bounds hk3 hk5 hv hVL hRM hRMo hcs asinC hrr hpos hx).2.2
  · refine le_trans hρ1 (mul_le_mul_of_nonneg_right (le_trans hs2 (fx_le_iff.mpr (le_max_left _ _))) hvol0)
  · refine le_trans hρ2 (mul_le_mul_of_nonneg_right ?_ hvol0)
    have hS0 : 0 ≤ ∑ i, ∑ j, (if i < j ∧ √(dminSq (R i) (R j)) < 2 then
        (nuCountSeg c (fun i => (R i).eps) (fun i j => √(dminSq (R i) (R j))) (fun i j => √(dmaxSq (R i) (R j)))
          (codeFirst k lo hi) i j : ℝ) *
        √(3 * lamT (√(dmaxSq (R i) (R j))) (codeFirst k lo hi i j) ^ 2 *
            (8 * (m4pt (halfSides k (realLo k lo) (realLo k hi) i) + m4pt (halfSides k (realLo k lo) (realLo k hi) j))) +
          3 * muT (√(dminSq (R i) (R j))) (√(dmaxSq (R i) (R j))) (codeFirst k lo hi i j) ^ 2 *
            (m2pt (halfSides k (realLo k lo) (realLo k hi) i) + m2pt (halfSides k (realLo k lo) (realLo k hi) j) +
              2 * √(m2pt (halfSides k (realLo k lo) (realLo k hi) i)) *
                √(m2pt (halfSides k (realLo k lo) (realLo k hi) j))) +
          3 * min ((8 * (m4pt (halfSides k (realLo k lo) (realLo k hi) i) +
              m4pt (halfSides k (realLo k lo) (realLo k hi) j))) / √(dminSq (R i) (R j)) ^ 2)
            (π ^ 2 * (m2pt (halfSides k (realLo k lo) (realLo k hi) i) +
              m2pt (halfSides k (realLo k lo) (realLo k hi) j) +
              2 * √(m2pt (halfSides k (realLo k lo) (realLo k hi) i)) *
                √(m2pt (halfSides k (realLo k lo) (realLo k hi) j))))) else 0) := by
      refine Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => ?_))
      split_ifs
      · exact mul_nonneg (Nat.cast_nonneg _) (Real.sqrt_nonneg _)
      · exact le_refl 0
    have hle := le_trans hs3 (fx_le_iff.mpr (le_max_left rr.sEr2 0))
    exact pow_le_pow_left₀ hS0 hle 2
  · intro x hx
    obtain ⟨hlin, hρx0, -⟩ := area_lin_bounds hk3 hk5 hv hVL hRM hRMo hcs asinC hrr hpos hx
    rw [abs_le] at hlin
    have hπ : π ≤ unionArea (xcfg k x) := hPi k (xcfg k x) (by omega)
    have hAypos : 0 < unionArea (xcfg k x) := lt_of_lt_of_le Real.pi_pos hπ
    have hx0 : 0 ≤ xget x 0 := by
      rw [xget_of_lt x h0m]
      have := (hx ⟨0, h0m⟩ (Set.mem_univ _)).1
      exact le_trans (fx_nonneg_iff.mpr hlo0) this
    unfold leafF phiS
    apply ENNReal.ofReal_le_ofReal
    apply mul_le_mul_of_nonneg_left _ hx0
    have hs : 0 ≤ (k : ℝ) - 1 / 2 := by
      have : (3 : ℝ) ≤ k := by exact_mod_cast hk3
      linarith
    exact Real.rpow_le_rpow_of_nonpos hAypos (by linarith [hlin.2]) (by linarith)

end BHH
