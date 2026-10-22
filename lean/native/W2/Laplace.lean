/-
Module L: `LaplaceBound k`, from the Laplace/Tonelli identity (`laplace_lhs_eq`), the window-2 area
bound (`unionArea_psum_le`, `pi_le_unionArea_psum`) and sorted coordinates (`sorted_coords`).
-/
import W2.LapSorted

open MeasureTheory Set Real
open scoped ENNReal

noncomputable section

namespace BHH.W2

theorem laplaceBound (k : ℕ) : LaplaceBound k := by
  intro hk
  rw [laplace_lhs_eq k hk]
  set s : ℝ := (k : ℝ) - 1 / 2 with hsdef
  have hs : 0 < s := by
    have : (3 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have hG : 0 ≤ Real.Gamma s := (Real.Gamma_pos_of_pos hs).le
  have hHm : MeasurableSet {z : Fin (k - 1) → Pt | ∀ i, z i ∈ Hp} := by
    have : {z : Fin (k - 1) → Pt | ∀ i, z i ∈ Hp} = ⋂ i, {z | 0 < (z i).1} := by ext z; simp [Hp]
    rw [this]
    exact MeasurableSet.iInter fun i => measurableSet_lt measurable_const ((measurable_pi_apply i).fst)
  set I := ∫⁻ z in {z : Fin (k - 1) → Pt | ∀ i, z i ∈ Hp}, ENNReal.ofReal (ghat z * unionArea (psum z) ^ (-s))
    with hIdef
  -- the window-2 area bound, pointwise
  have hA : ∫⁻ z, Set.indicator {z : Fin (k - 1) → Pt | ∀ i, z i ∈ Hp}
      (fun z => ENNReal.ofReal (ghat z * (Real.Gamma s * (π + Xsum z) ^ (-s)))) z ≤
      ENNReal.ofReal (Real.Gamma s) * I := by
    rw [lintegral_indicator hHm, hIdef, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono fun z => ?_
    rw [← ENNReal.ofReal_mul hG]
    refine ENNReal.ofReal_le_ofReal ?_
    have hA1 : π ≤ unionArea (psum z) := pi_le_unionArea_psum z
    have hpow : (π + Xsum z) ^ (-s) ≤ unionArea (psum z) ^ (-s) :=
      Real.rpow_le_rpow_of_nonpos (by linarith [Real.pi_pos]) (unionArea_psum_le z) (by linarith)
    calc ghat z * (Real.Gamma s * (π + Xsum z) ^ (-s)) = Real.Gamma s * (ghat z * (π + Xsum z) ^ (-s)) := by ring
      _ ≤ Real.Gamma s * (ghat z * unionArea (psum z) ^ (-s)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpow (ghat_nonneg z)) hG
  -- sorted coordinates
  have hsc := sorted_coords (m := k - 1) s (by omega) k (by omega)
  have hexp : ((k - 1 : ℕ) : ℝ) + 1 - 1 / 2 = s := by
    rw [Nat.cast_sub (by omega : 1 ≤ k), hsdef]; push_cast; ring
  have hJ : ∫⁻ w : Fin (k - 1) → Pt, ENNReal.ofReal (ckIntegrand (k - 1) w) =
      ∫⁻ w : Fin (k - 1) → Pt, ENNReal.ofReal (dcG (unitGraph (cfg w)) * unionArea (cfg w) ^ (-s)) := by
    simp only [ckIntegrand, hexp]
  -- the constants
  have hkf : (0 : ℝ) < k.factorial := Nat.cast_pos.2 (Nat.factorial_pos k)
  have key : ENNReal.ofReal (1 / 2) * ENNReal.ofReal (Real.Gamma s) =
      ENNReal.ofReal (Real.Gamma s / (2 * k.factorial)) * (k.factorial : ℝ≥0∞) := by
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    field_simp
  calc ENNReal.ofReal (1 / 2) * ∫⁻ z, Set.indicator {z : Fin (k - 1) → Pt | ∀ i, z i ∈ Hp}
        (fun z => ENNReal.ofReal (ghat z * (Real.Gamma s * (π + Xsum z) ^ (-s)))) z
      ≤ ENNReal.ofReal (1 / 2) * (ENNReal.ofReal (Real.Gamma s) * I) := mul_le_mul_right hA _
    _ = ENNReal.ofReal (Real.Gamma s / (2 * k.factorial)) * ((k.factorial : ℝ≥0∞) * I) := by
        rw [← mul_assoc, key, mul_assoc]
    _ ≤ ENNReal.ofReal (Real.Gamma s / (2 * k.factorial)) *
          ∫⁻ w : Fin (k - 1) → Pt, ENNReal.ofReal (dcG (unitGraph (cfg w)) * unionArea (cfg w) ^ (-s)) :=
        mul_le_mul_right hsc _
    _ = C k := by rw [C, hJ]

end BHH.W2
