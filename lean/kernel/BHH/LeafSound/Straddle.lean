/-
Module D, part 17: the straddle branch (`StraddleSpec`), from Prop 3.7 (`StraddleProp`) and Lemma 3.5
(`EventBoundProp`).
-/
import BHH.LeafSound.Top

open BHH.Cert Real MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace BHH

lemma fx_ONE_D : fx ONE = 1 := by unfold fx; rw [ONE_cast]; unfold SC; field_simp

/-- `evLB` is below the real bound of Lemma 3.5 (or the bound is negative and `evLB = 0`) -/
lemma evLB_le {q fmin fmax val : ℤ} (hq : 0 ≤ q) (hmin : 0 ≤ fmin) (hmax : 0 ≤ fmax) :
    fx (evLB q fmin fmax val) = 0 ∨
      fx (evLB q fmin fmax val) ≤ max (fx q * fx fmin) (fx val - (1 - fx q) * fx fmax) := by
  unfold evLB
  simp only
  rw [fx_max, fx_max, fx_zero]
  by_cases h : max (fx (shrD (q * fmin) PR)) (fx (val - shrU ((ONE - q) * fmax) PR)) ≤ 0
  · left; exact max_eq_right h
  · right
    push_neg at h
    rw [max_eq_left h.le]
    apply max_le_max
    · exact fx_shrD_mul_le q fmin
    · have h2 := fx_mul_le_shrU (ONE - q) fmax
      rw [fx_sub, fx_ONE_D] at h2
      rw [fx_sub]
      linarith

theorem straddleSpec_of {k : ℕ} (hk3 : 3 ≤ k) {gt : GTab} (hgt : GTabSound k gt)
    (hEv : EventBoundProp) (hSt : StraddleProp) : StraddleSpec k gt := by
  intro lo hi hv j hj2 hjk hlo0 hlo2 hord f fminLo fmaxHi val hfmin0 hfmax0 hval0 hfmin hfmax hval hg0
  intro P Q pord
  obtain ⟨hset, hvolF⟩ := hSt k lo hi j hv hj2 hjk hlo0 hlo2 hord
  set F := {x ∈ (boxOf lo hi : Set (Fin (mDim k) → ℝ)) | xget x (2 * j - 3) ≤ xget x (2 * (j + 1) - 3)} with hF
  have hFm : MeasurableSet F := by
    rw [← hset]; exact (measurableSet_boxOf' lo hi).inter (measurableSet_Dk_leaf k)
  have hFQ : F ⊆ (boxOf lo hi : Set (Fin (mDim k) → ℝ)) := fun x hx => hx.1
  have hpord0 : 0 ≤ pord := le_max_right _ _
  have hq0 : 0 ≤ fx pord := fx_nonneg_iff.mpr hpord0
  have hvolq : ENNReal.ofReal (fx pord * (volume (boxOf lo hi : Set (Fin (mDim k) → ℝ))).toReal) ≤ volume F := by
    have hP2 : P = (ptBoxes k lo hi).getD j default := rfl
    by_cases hc : 0 ≤ (cdfIv P.xl P.xh Q.xl Q.xh 0).lo
    · have e : pord = (cdfIv P.xl P.xh Q.xl Q.xh 0).lo := max_eq_left hc
      rw [e]
      obtain ⟨hxl, hxh, _⟩ := ptBoxes_xl_xh (k := k) lo hi hj2 (by omega)
      obtain ⟨hxl', hxh', _⟩ := ptBoxes_xl_xh (k := k) lo hi (by omega : 2 ≤ j + 1) hjk
      have : (cdfIv P.xl P.xh Q.xl Q.xh 0) = cdfIv (lo.getD (2 * j - 3) 0) (hi.getD (2 * j - 3) 0)
          (lo.getD (2 * (j + 1) - 3) 0) (hi.getD (2 * (j + 1) - 3) 0) 0 := by
        show cdfIv ((ptBoxes k lo hi).getD j default).xl ((ptBoxes k lo hi).getD j default).xh
          ((ptBoxes k lo hi).getD (j + 1) default).xl ((ptBoxes k lo hi).getD (j + 1) default).xh 0 = _
        rw [hxl, hxh, hxl', hxh']; rfl
      rw [this]; exact hvolF
    · push_neg at hc
      have e : pord = 0 := max_eq_right hc.le
      rw [e, fx_zero, zero_mul, ENNReal.ofReal_zero]; exact zero_le
  have hE := hEv (mDim k) (boxOf lo hi) F f (fx pord) (fx fminLo) (fx fmaxHi) (fx val)
    (measurableSet_boxOf' lo hi) hFm hFQ (volume_boxOf_ne_top lo hi) hq0 (fx_nonneg_iff.mpr hfmin0)
    (fx_nonneg_iff.mpr hfmax0) hvolq hfmin hfmax hval
  -- `∫_{box ∩ D_k} 2g f ≥ gmin ∫_F f`
  have hg0' : (0 : ℝ) ≤ gt.gmin (val3 (stCode k lo hi)) := by exact_mod_cast hg0
  have hint : ENNReal.ofReal (gt.gmin (val3 (stCode k lo hi)) : ℝ) * ∫⁻ x in F, f x ≤
      ∫⁻ x in boxOf lo hi ∩ Dk k, ENNReal.ofReal (2 * dcG (unitGraph (xcfg k x))) * f x := by
    rw [hset, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine setLIntegral_mono' hFm (fun x hx => ?_)
    gcongr
    exact gmin_le_two_g hk3 hgt hx.1
  refine le_trans ?_ hint
  have hvol0 : 0 ≤ (volume (boxOf lo hi : Set (Fin (mDim k) → ℝ))).toReal := ENNReal.toReal_nonneg
  have hfx : fx (gt.gmin (val3 (stCode k lo hi)) * evLB pord fminLo fmaxHi val) =
      (gt.gmin (val3 (stCode k lo hi)) : ℝ) * fx (evLB pord fminLo fmaxHi val) := by
    unfold fx; push_cast; ring
  rw [hfx]
  rcases evLB_le (val := val) hpord0 hfmin0 hfmax0 with h0 | hle
  · rw [h0, mul_zero, mul_zero, ENNReal.ofReal_zero]; exact zero_le
  · calc ENNReal.ofReal ((volume (boxOf lo hi : Set (Fin (mDim k) → ℝ))).toReal *
          ((gt.gmin (val3 (stCode k lo hi)) : ℝ) * fx (evLB pord fminLo fmaxHi val)))
        ≤ ENNReal.ofReal ((gt.gmin (val3 (stCode k lo hi)) : ℝ) *
            ((volume (boxOf lo hi : Set (Fin (mDim k) → ℝ))).toReal *
              max (fx pord * fx fminLo) (fx val - (1 - fx pord) * fx fmaxHi))) := by
          apply ENNReal.ofReal_le_ofReal
          calc (volume (boxOf lo hi : Set (Fin (mDim k) → ℝ))).toReal *
                ((gt.gmin (val3 (stCode k lo hi)) : ℝ) * fx (evLB pord fminLo fmaxHi val))
              = (gt.gmin (val3 (stCode k lo hi)) : ℝ) * ((volume (boxOf lo hi : Set (Fin (mDim k) → ℝ))).toReal *
                  fx (evLB pord fminLo fmaxHi val)) := by ring
            _ ≤ _ := by gcongr
      _ = ENNReal.ofReal (gt.gmin (val3 (stCode k lo hi)) : ℝ) *
            ENNReal.ofReal ((volume (boxOf lo hi : Set (Fin (mDim k) → ℝ))).toReal *
              max (fx pord * fx fminLo) (fx val - (1 - fx pord) * fx fmaxHi)) := ENNReal.ofReal_mul hg0'
      _ ≤ _ := by gcongr

end BHH
