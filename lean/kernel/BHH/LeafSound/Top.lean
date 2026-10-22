/-
Module D, top level: `LeafSoundProp k` for the leaf function, by the case analysis of the code.
-/
import BHH.LeafSound.FBounds

open BHH.Cert Real MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace BHH

lemma st_eq (k : ℕ) (lo hi : List ℤ) :
    List.map (fun x : ℤ × ℤ => if x.2 ≤ ONE * ONE then (1 : ℕ) else if ONE * ONE < x.1 then 0 else 2)
      (List.map (fun x : ℕ × ℕ => d2minmax ((ptBoxes k lo hi).getD x.1 default)
        ((ptBoxes k lo hi).getD x.2 default)) (pairList k)) = stCode k lo hi := rfl

lemma measurableSet_boxOf' {m : ℕ} (lo hi : List ℤ) : MeasurableSet (boxOf lo hi : Set (Fin m → ℝ)) :=
  MeasurableSet.univ_pi (fun _ => measurableSet_Ico)

lemma volume_boxOf_ne_top {m : ℕ} (lo hi : List ℤ) : volume (boxOf lo hi : Set (Fin m → ℝ)) ≠ ⊤ := by
  unfold boxOf; rw [Real.volume_pi_Ico]
  exact ENNReal.prod_ne_top (fun _ _ => ENNReal.ofReal_ne_top)

/-- a constant pointwise lower bound on a box inside `D_k` -/
lemma lintegral_box_const_le {k : ℕ} {lo hi : List ℤ} (hsub : (boxOf lo hi : Set (Fin (mDim k) → ℝ)) ⊆ Dk k)
    {c : ℝ} {F : (Fin (mDim k) → ℝ) → ℝ≥0∞} (hF : ∀ x ∈ (boxOf lo hi : Set (Fin (mDim k) → ℝ)), ENNReal.ofReal c ≤ F x) :
    ENNReal.ofReal ((volume (boxOf lo hi : Set (Fin (mDim k) → ℝ))).toReal * c) ≤
      ∫⁻ x in boxOf lo hi ∩ Dk k, F x := by
  rw [Set.inter_eq_left.mpr hsub]
  calc ENNReal.ofReal ((volume (boxOf lo hi : Set (Fin (mDim k) → ℝ))).toReal * c)
      = ENNReal.ofReal c * volume (boxOf lo hi : Set (Fin (mDim k) → ℝ)) := by
        rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal (volume_boxOf_ne_top lo hi), mul_comm]
    _ = ∫⁻ x in boxOf lo hi, ENNReal.ofReal c := (setLIntegral_const _ _).symm
    _ ≤ ∫⁻ x in boxOf lo hi, F x := setLIntegral_mono' (measurableSet_boxOf' lo hi) hF

lemma shrD_zero' (a : ℤ) : shrD a 0 = a := by unfold shrD; simp

lemma lintegral_F2_ge {k : ℕ} (S : Set (Fin (mDim k) → ℝ)) (hS : MeasurableSet S) :
    ∫⁻ x in S, ENNReal.ofReal (2 * dcG (unitGraph (xcfg k x))) * leafF k x ≤ ∫⁻ x in S, F2 k x :=
  setLIntegral_mono' hS (fun x _ => F2_ge k x)

theorem leafSound_top {k : ℕ} (hk3 : 3 ≤ k) (hk5 : k ≤ 5) {gt : GTab} (hgt : GTabSound k gt)
    {cs : ℤ → Iv × Iv} (hcs : CosSinSound cs) (cand : CandFn) (asinC : AsinFn)
    (hgt0 : ∀ idx, idx < 3 ^ (pairList k).length → 0 ≤ gt.gmin idx)
    (hG : GreenFormula) (hVL : VertexLemmaSeg) (hUS : UnionSoundProp) (hB : BracketProp) (hRM : RemMaxProp)
    (hRMo : RemMomentsProp) (hPi : UnionAreaGePiProp)
    (hP38 : Prop38Spec k gt cs cand) (hStr : StraddleSpec k gt) (hEx : ExtraSpec k gt) :
    LeafSoundProp k (fun lo hi => (leafLB k gt cs cand asinC lo hi).val) := by
  intro lo hi hv
  show ENNReal.ofReal (((leafLB k gt cs cand asinC lo hi).val : ℝ) / 2 ^ OS) ≤ _
  rw [leafLB_eq_alt]
  unfold leafAlt
  dsimp only
  split
  · simp
  rename_i hout
  obtain ⟨hlo0, hlo2⟩ := lo_nonneg_of_not_outside hk3 hout
  rw [st_eq, fold_idx3]
  split
  · -- Prop 3.8: some pair with d⁻ = 0
    split
    · simp
    rename_i hcond
    simp only [not_not] at hcond
    obtain ⟨hn0, hgpos, hlo0pos⟩ := hcond
    split
    · simp
    rename_i u hu
    have hsub := boxOf_subset_Dk hk3 hv hlo0 hlo2 (ord_of_strad_nil (by simpa using hn0))
    refine le_trans (ENNReal.ofReal_le_ofReal (finish_le hk3 hv _)) ?_
    exact lintegral_box_const_le hsub (fun x hx => hP38 lo hi hv hlo0pos hgpos u hu x hx)
  · -- all pairs with d⁻ > 0
    rename_i hno3e
    have hpos := dminSq_pos_of_no3e hno3e
    split
    · simp
    rename_i hneed
    split
    · simp
    rename_i u hu
    split
    · simp
    rename_i rr hrr
    split
    · simp
    rename_i fLowA f1 f2 hlowA
    refine le_trans (ENNReal.ofReal_le_ofReal (finish_le hk3 hv _)) ?_
    obtain ⟨hfb, hfmin0, hfmax0⟩ :=
      leafF_bounds hk3 hk5 hv hG hUS hVL hRM hRMo hPi hcs cand asinC hu hrr hpos hlo0 hlowA
    have hbr := bracket_input hk3 hk5 hv hG hUS hVL hRM hRMo hPi hB hcs cand asinC hu hrr hpos hlo0
    have hval0 := bracketVal_nonneg k (gradList k u) (widthList k lo hi) u.A (sumAbs (gradList k u) (widthList k lo hi))
      (sumSq (gradList k u) (widthList k lo hi)) rr (listGet lo 0) (listGet hi 0)
    have hidx : val3 (stCode k lo hi) < 3 ^ (pairList k).length := by
      have := val3_lt3 (stCode k lo hi) (stCode_lt3 k lo hi); rwa [stCode_length] at this
    have hg0 := hgt0 _ hidx
    set strad := List.filter (fun j => decide (((ptBoxes k lo hi).getD j default).xh >
      ((ptBoxes k lo hi).getD (j + 1) default).xl)) (List.filter (fun j => decide (2 ≤ j ∧ j + 1 < k)) (List.range k))
      with hstrad
    have hstradC : stradC k lo hi = strad := rfl
    have hvol0 : 0 ≤ (volume (boxOf lo hi : Set (Fin (mDim k) → ℝ))).toReal := ENNReal.toReal_nonneg
    rcases hcase : strad with _ | ⟨j, _ | ⟨j2, rest⟩⟩
    · -- no straddling pair: the box lies in D_k
      have hlen : (stradC k lo hi).length = 0 := by rw [hstradC, hcase]; rfl
      have hsub := boxOf_subset_Dk hk3 hv hlo0 hlo2 (ord_of_strad_nil hlen)
      rw [Set.inter_eq_left.mpr hsub]
      refine le_trans ?_ (lintegral_F2_ge _ (measurableSet_boxOf' lo hi))
      have h01 : ((0 : ℕ) == 1) = false := rfl
      simp only [List.length_nil, beq_self_eq_true, true_and, h01, Bool.false_eq_true, false_and, if_false]
      rw [hcase] at hneed
      simp only [List.length_nil, beq_self_eq_true, true_and, h01, Bool.false_eq_true, false_and, or_false,
        not_not] at hneed
      by_cases hE : gt.gmin (val3 (stCode k lo hi)) < gt.gmax (val3 (stCode k lo hi)) ∧
          0 < gt.gmax (val3 (stCode k lo hi))
      · rw [if_pos hE]
        have hX := hEx lo hi hv (leafF k) _ _ _ hfmin0 hfmax0 hval0 (fun x hx => (hfb x hx).1)
          (fun x hx => (hfb x hx).2) hbr hg0
        simp only at hX
        refine le_trans (le_of_eq ?_) hX
        congr 2
        rw [fx_add']
        congr 1
        split_ifs with hgp
        · rw [shrD_zero']; unfold fx; push_cast; ring
        · have : gt.gmin (val3 (stCode k lo hi)) = 0 := by omega
          rw [this, fx_zero]; simp
      · rw [if_neg hE]
        have hgp : 0 < gt.gmin (val3 (stCode k lo hi)) := by tauto
        rw [if_pos hgp, shrD_zero', add_zero]
        have hfx : fx (gt.gmin (val3 (stCode k lo hi)) * bracketVal k (gradList k u) (widthList k lo hi) u.A
            (sumAbs (gradList k u) (widthList k lo hi)) (sumSq (gradList k u) (widthList k lo hi)) rr (listGet lo 0)
            (listGet hi 0)) = (gt.gmin (val3 (stCode k lo hi)) : ℝ) * fx (bracketVal k (gradList k u)
            (widthList k lo hi) u.A (sumAbs (gradList k u) (widthList k lo hi))
            (sumSq (gradList k u) (widthList k lo hi)) rr (listGet lo 0) (listGet hi 0)) := by
          unfold fx; push_cast; ring
        rw [hfx]
        have hg0' : (0 : ℝ) ≤ gt.gmin (val3 (stCode k lo hi)) := by exact_mod_cast hg0
        calc ENNReal.ofReal ((volume (boxOf lo hi : Set (Fin (mDim k) → ℝ))).toReal *
              ((gt.gmin (val3 (stCode k lo hi)) : ℝ) * fx (bracketVal k (gradList k u) (widthList k lo hi) u.A
                (sumAbs (gradList k u) (widthList k lo hi)) (sumSq (gradList k u) (widthList k lo hi)) rr
                (listGet lo 0) (listGet hi 0))))
            = ENNReal.ofReal (gt.gmin (val3 (stCode k lo hi)) : ℝ) *
                ENNReal.ofReal ((volume (boxOf lo hi : Set (Fin (mDim k) → ℝ))).toReal *
                  fx (bracketVal k (gradList k u) (widthList k lo hi) u.A
                    (sumAbs (gradList k u) (widthList k lo hi)) (sumSq (gradList k u) (widthList k lo hi)) rr
                    (listGet lo 0) (listGet hi 0))) := by
              rw [← ENNReal.ofReal_mul hg0']; congr 1; ring
          _ ≤ ENNReal.ofReal (gt.gmin (val3 (stCode k lo hi)) : ℝ) * ∫⁻ x in boxOf lo hi, leafF k x := by
              gcongr
          _ = ∫⁻ x in boxOf lo hi, ENNReal.ofReal (gt.gmin (val3 (stCode k lo hi)) : ℝ) * leafF k x := by
              rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          _ ≤ ∫⁻ x in boxOf lo hi, ENNReal.ofReal (2 * dcG (unitGraph (xcfg k x))) * leafF k x := by
              refine setLIntegral_mono' (measurableSet_boxOf' lo hi) (fun x hx => ?_)
              gcongr
              exact gmin_le_two_g hk3 hgt hx
    · -- one straddling pair
      have hs1 : stradC k lo hi = [j] := by rw [hstradC, hcase]
      obtain ⟨⟨hj2, hjk⟩, hord⟩ := ord_of_strad_single hs1
      refine le_trans ?_ (lintegral_F2_ge _ ((measurableSet_boxOf' lo hi).inter ?_))
      · have h10 : ((1 : ℕ) == 0) = false := rfl
        simp only [List.length_cons, List.length_nil, zero_add, beq_self_eq_true, true_and, h10,
          Bool.false_eq_true, false_and, if_false, zero_add]
        split_ifs with hgp
        · exact hStr lo hi hv j hj2 hjk hlo0 (fun _ => hlo2) hord (leafF k) _ _ _ hfmin0 hfmax0 hval0
            (fun x hx => (hfb x hx).1) (fun x hx => (hfb x hx).2) hbr hg0
        · simp [fx_zero]
      · exact measurableSet_Dk_leaf k
    · -- two or more straddling pairs: nothing to do
      rw [hcase] at hneed
      simp at hneed

end BHH
