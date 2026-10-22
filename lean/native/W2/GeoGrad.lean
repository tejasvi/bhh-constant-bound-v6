/-
Module G: `|∇_{y_i} A| ≤ 2` (`GreenGradLe`): for any `E ⊆ [0, 2π)` and `V = ∫_E u(t) dt`,
`|V|² = ∫_E ⟨V, u⟩ ≤ ∫_0^{2π} ⟨V, u⟩_+ = 2 |V|`.
-/
import W2.GeoProps

open MeasureTheory Set Real

noncomputable section

namespace BHH.W2

open BHH

/-- `∫_0^{2π} max(cos(t - α), 0) dt = 2` -/
lemma integral_pos_part_cos_shift (α : ℝ) :
    ∫ t in (0 : ℝ)..(2 * π), max (Real.cos (t - α)) 0 = 2 := by
  have hg : Continuous fun u : ℝ => max (Real.cos u) 0 := by fun_prop
  rw [intervalIntegral.integral_comp_sub_right (fun u => max (Real.cos u) 0) α]
  have hper : Function.Periodic (fun u : ℝ => max (Real.cos u) 0) (2 * π) := by
    intro u; simp only [Real.cos_add_two_pi]
  have e1 : (2 * π - α) = -α + 2 * π := by ring
  rw [show (0 : ℝ) - α = -α by ring, e1, hper.intervalIntegral_add_eq (-α) (-(π / 2))]
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := π / 2) (hg.intervalIntegrable _ _)
    (hg.intervalIntegrable _ _)]
  have h1 : ∫ u in (-(π / 2))..(π / 2), max (Real.cos u) 0 = ∫ u in (-(π / 2))..(π / 2), Real.cos u := by
    refine intervalIntegral.integral_congr fun u hu => ?_
    rw [uIcc_of_le (by linarith [Real.pi_pos])] at hu
    exact max_eq_left (Real.cos_nonneg_of_mem_Icc hu)
  have h2 : ∫ u in (π / 2)..(-(π / 2) + 2 * π), max (Real.cos u) 0 = ∫ u in (π / 2)..(-(π / 2) + 2 * π), (0 : ℝ) := by
    refine intervalIntegral.integral_congr fun u hu => ?_
    rw [uIcc_of_le (by linarith [Real.pi_pos])] at hu
    refine max_eq_right ?_
    exact Real.cos_nonpos_of_pi_div_two_le_of_le hu.1 (by linarith [hu.2])
  rw [h1, h2, integral_cos, intervalIntegral.integral_zero, Real.sin_neg, Real.sin_pi_div_two]
  ring

/-- `|∫_E u| ≤ 2` for every `E ⊆ [0, 2π)` -/
theorem grad_sq_le_four (E : Set ℝ) (hE : E ⊆ Ico 0 (2 * π)) :
    (∫ t in E, Real.cos t) ^ 2 + (∫ t in E, Real.sin t) ^ 2 ≤ 4 := by
  set V1 := ∫ t in E, Real.cos t with hV1
  set V2 := ∫ t in E, Real.sin t with hV2
  have hEI : E ⊆ Icc 0 (2 * π) := hE.trans Ico_subset_Icc_self
  have hint : ∀ f : ℝ → ℝ, Continuous f → IntegrableOn f E := fun f hf =>
    (hf.integrableOn_Icc (a := 0) (b := 2 * π)).mono_set hEI
  have hintI : ∀ f : ℝ → ℝ, Continuous f → IntegrableOn f (Icc 0 (2 * π)) := fun f hf => hf.integrableOn_Icc
  -- `N = |V|` and its polar angle
  set N := Real.sqrt (V1 ^ 2 + V2 ^ 2) with hN
  have hN0 : 0 ≤ N := Real.sqrt_nonneg _
  have hNsq : N ^ 2 = V1 ^ 2 + V2 ^ 2 := Real.sq_sqrt (by positivity)
  obtain ⟨α, hα1, hα2⟩ : ∃ α, V1 = N * Real.cos α ∧ V2 = N * Real.sin α := by
    refine ⟨Complex.arg ⟨V1, V2⟩, ?_, ?_⟩
    · have := Complex.norm_mul_cos_arg ⟨V1, V2⟩
      rw [Complex.norm_eq_sqrt_sq_add_sq] at this
      exact this.symm
    · have := Complex.norm_mul_sin_arg ⟨V1, V2⟩
      rw [Complex.norm_eq_sqrt_sq_add_sq] at this
      exact this.symm
  -- `N² = ∫_E ⟨V, u⟩ ≤ ∫_E ⟨V, u⟩_+ ≤ ∫_0^{2π} ⟨V, u⟩_+ = 2 N`
  have hlin : V1 ^ 2 + V2 ^ 2 = ∫ t in E, (V1 * Real.cos t + V2 * Real.sin t) := by
    rw [integral_add ((hint _ continuous_cos).const_mul V1) ((hint _ continuous_sin).const_mul V2),
      integral_const_mul, integral_const_mul, ← hV1, ← hV2]
    ring
  have hpos : Continuous fun t : ℝ => max (V1 * Real.cos t + V2 * Real.sin t) 0 := by fun_prop
  have hm1 : ∫ t in E, (V1 * Real.cos t + V2 * Real.sin t) ≤ ∫ t in E, max (V1 * Real.cos t + V2 * Real.sin t) 0 :=
    integral_mono ((hint _ continuous_cos).const_mul V1 |>.add ((hint _ continuous_sin).const_mul V2))
      (hint _ hpos) fun t => le_max_left _ _
  have hm2 : ∫ t in E, max (V1 * Real.cos t + V2 * Real.sin t) 0 ≤
      ∫ t in Icc 0 (2 * π), max (V1 * Real.cos t + V2 * Real.sin t) 0 :=
    setIntegral_mono_set (hintI _ hpos) (Filter.Eventually.of_forall fun t => le_max_right _ _)
      hEI.eventuallyLE
  have hval : ∫ t in Icc 0 (2 * π), max (V1 * Real.cos t + V2 * Real.sin t) 0 = 2 * N := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by positivity)]
    have e : ∀ t, max (V1 * Real.cos t + V2 * Real.sin t) 0 = N * max (Real.cos (t - α)) 0 := by
      intro t
      rw [mul_max_of_nonneg _ _ hN0, mul_zero, Real.cos_sub, hα1, hα2]
      congr 1; ring
    simp_rw [e]
    rw [intervalIntegral.integral_const_mul, integral_pos_part_cos_shift]
    ring
  have hNle : N ^ 2 ≤ 2 * N := by
    rw [hNsq, hlin]; linarith
  have hN2 : N ≤ 2 := by
    rcases eq_or_lt_of_le hN0 with h | h
    · rw [← h]; norm_num
    · nlinarith
  rw [← hNsq]
  nlinarith

theorem greenGradLe : GreenGradLe := by
  intro k y i
  unfold greenGrad
  exact grad_sq_le_four (exposed y i) (fun t ht => ht.1)

end BHH.W2
