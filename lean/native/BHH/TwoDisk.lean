/-
Module B, corollary for the window-2 part: the area of the union of two unit disks at real distance `r`, from Green's formula
(2.1).  For `0 < r < 2` the exposed directions are `[α, 2π - α]` on the disk at the origin and
`[0, 2π) \ (π - α, π + α)` on the disk at `(r, 0)`, `α = arccos(r/2)`; for `r ≥ 2` both are `[0, 2π)`.
-/
import BHH.Defs

open MeasureTheory Set Real

namespace BHH

noncomputable section

namespace TD

/-- the configuration `(0, 0), (r, 0)` -/
def two (r : ℝ) : Fin 2 → Pt := ![(0, 0), (r, 0)]

lemma two_zero (r : ℝ) : two r 0 = (0, 0) := rfl
lemma two_one (r : ℝ) : two r 1 = (r, 0) := rfl

lemma sqDist_dir0 (r t : ℝ) : sqDist ((0, 0) + dir t) (r, 0) = 1 - 2 * r * Real.cos t + r ^ 2 := by
  simp only [sqDist, dir, Prod.mk_add_mk, zero_add, sub_zero]
  linear_combination Real.sin_sq_add_cos_sq t

lemma sqDist_dir1 (r t : ℝ) : sqDist ((r, 0) + dir t) (0, 0) = 1 + 2 * r * Real.cos t + r ^ 2 := by
  simp only [sqDist, dir, Prod.mk_add_mk, zero_add, sub_zero]
  linear_combination Real.sin_sq_add_cos_sq t

lemma exposed_two_zero (r : ℝ) :
    exposed (two r) 0 = {t | t ∈ Ico 0 (2 * π) ∧ 2 * r * Real.cos t ≤ r ^ 2} := by
  ext t
  simp only [exposed, Set.mem_setOf_eq, Fin.forall_fin_two, ne_eq, not_true_eq_false, false_implies,
    Fin.one_eq_zero_iff, OfNat.ofNat_ne_one, not_false_eq_true, true_implies, true_and, two_zero, two_one,
    sqDist_dir0]
  constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1, by linarith⟩

lemma exposed_two_one (r : ℝ) :
    exposed (two r) 1 = {t | t ∈ Ico 0 (2 * π) ∧ -(r ^ 2) ≤ 2 * r * Real.cos t} := by
  ext t
  simp only [exposed, Set.mem_setOf_eq, Fin.forall_fin_two, ne_eq, not_true_eq_false, false_implies,
    Fin.zero_eq_one_iff, OfNat.ofNat_ne_one, not_false_eq_true, true_implies, and_true, two_zero, two_one,
    sqDist_dir1]
  constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1, by linarith⟩

/-! ## cos on `[0, 2π)` -/

/-- for `t ∈ [0, 2π)` and `α ∈ [0, π]`: `cos t ≤ cos α ↔ α ≤ t ≤ 2π - α` -/
lemma cos_le_cos_iff {t α : ℝ} (ht : t ∈ Ico 0 (2 * π)) (hα0 : 0 ≤ α) (hαπ : α ≤ π) :
    Real.cos t ≤ Real.cos α ↔ α ≤ t ∧ t ≤ 2 * π - α := by
  rcases le_or_gt t π with htπ | htπ
  · rw [Real.strictAntiOn_cos.le_iff_ge ⟨ht.1, htπ⟩ ⟨hα0, hαπ⟩]
    constructor
    · intro h; exact ⟨h, by linarith⟩
    · intro h; exact h.1
  · have hs : 2 * π - t ∈ Icc 0 π := ⟨by linarith [ht.2], by linarith⟩
    have hc : Real.cos t = Real.cos (2 * π - t) := by rw [Real.cos_two_pi_sub]
    rw [hc, Real.strictAntiOn_cos.le_iff_ge hs ⟨hα0, hαπ⟩]
    constructor
    · intro h; exact ⟨by linarith, by linarith⟩
    · intro h; linarith [h.2]

/-- for `t ∈ [0, 2π)` and `α ∈ [0, π]`: `cos (π - α) ≤ cos t ↔ t ∉ (π - α, π + α)` -/
lemma cos_pi_sub_le_iff {t α : ℝ} (ht : t ∈ Ico 0 (2 * π)) (hα0 : 0 ≤ α) (hαπ : α ≤ π) :
    Real.cos (π - α) ≤ Real.cos t ↔ t ∉ Ioo (π - α) (π + α) := by
  rw [mem_Ioo, not_and_or, not_lt, not_lt]
  rcases le_or_gt t π with htπ | htπ
  · rw [Real.strictAntiOn_cos.le_iff_ge ⟨by linarith, by linarith⟩ ⟨ht.1, htπ⟩]
    constructor
    · intro h; exact Or.inl h
    · rintro (h | h)
      · exact h
      · linarith
  · have hs : 2 * π - t ∈ Icc 0 π := ⟨by linarith [ht.2], by linarith⟩
    have hc : Real.cos t = Real.cos (2 * π - t) := by rw [Real.cos_two_pi_sub]
    rw [hc, Real.strictAntiOn_cos.le_iff_ge ⟨by linarith, by linarith⟩ hs]
    constructor
    · intro h; exact Or.inr (by linarith)
    · rintro (h | h)
      · linarith
      · linarith

/-! ## integrals -/

lemma integral_one_add_mul_cos (r a b : ℝ) :
    ∫ t in a..b, (1 + r * Real.cos t) = (b - a) + r * (Real.sin b - Real.sin a) := by
  rw [intervalIntegral.integral_add intervalIntegrable_const
    ((Real.continuous_cos.const_mul r).intervalIntegrable a b), intervalIntegral.integral_const,
    intervalIntegral.integral_const_mul, integral_cos]
  simp

lemma setIntegral_Ico' {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) : ∫ t in Ico a b, f t = ∫ t in a..b, f t := by
  rw [intervalIntegral.integral_of_le hab, integral_Ico_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]

lemma setIntegral_Ioo' {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) : ∫ t in Ioo a b, f t = ∫ t in a..b, f t := by
  rw [intervalIntegral.integral_of_le hab, integral_Ioc_eq_integral_Ioo]

lemma setIntegral_Icc' {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) : ∫ t in Icc a b, f t = ∫ t in a..b, f t := by
  rw [intervalIntegral.integral_of_le hab, integral_Icc_eq_integral_Ioc]

/-! ## the two-disk area -/

lemma two_ne (r : ℝ) (hr : r ≠ 0) : ∀ i j : Fin 2, i ≠ j → two r i ≠ two r j := by
  intro i j hij
  fin_cases i <;> fin_cases j
  · exact absurd rfl hij
  · intro h; apply hr; have := congrArg Prod.fst h; simpa [two] using this.symm
  · intro h; apply hr; have := congrArg Prod.fst h; simpa [two] using this
  · exact absurd rfl hij

/-- `greenArea` of two unit disks at distance `r ∈ (0, 2)` -/
theorem greenArea_two {r : ℝ} (hr0 : 0 < r) (hr2 : r < 2) :
    greenArea (two r) = 2 * π - 2 * Real.arccos (r / 2) + r / 2 * √(4 - r ^ 2) := by
  set α := Real.arccos (r / 2) with hα
  have hα0 : 0 < α := Real.arccos_pos.mpr (by linarith)
  have hαπ2 : α < π / 2 := Real.arccos_lt_pi_div_two.mpr (by linarith)
  have hπ := Real.pi_pos
  have hcos : Real.cos α = r / 2 := Real.cos_arccos (by linarith) (by linarith)
  have hsin : Real.sin α = √(4 - r ^ 2) / 2 := by
    rw [hα, Real.sin_arccos, show (1 : ℝ) - (r / 2) ^ 2 = (4 - r ^ 2) / 4 by ring,
      Real.sqrt_div (by nlinarith) 4, show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  -- exposed sets
  have e0 : exposed (two r) 0 = Icc α (2 * π - α) := by
    rw [exposed_two_zero]
    ext t
    simp only [Set.mem_setOf_eq, mem_Icc]
    constructor
    · rintro ⟨ht, h⟩
      have h' : Real.cos t ≤ Real.cos α := by rw [hcos]; nlinarith
      exact (cos_le_cos_iff ht hα0.le (by linarith)).mp h'
    · rintro ⟨h1, h2⟩
      have ht : t ∈ Ico 0 (2 * π) := ⟨by linarith, by linarith⟩
      refine ⟨ht, ?_⟩
      have := (cos_le_cos_iff ht hα0.le (by linarith)).mpr ⟨h1, h2⟩
      rw [hcos] at this; nlinarith
  have e1 : exposed (two r) 1 = Ico 0 (2 * π) \ Ioo (π - α) (π + α) := by
    rw [exposed_two_one]
    ext t
    simp only [Set.mem_setOf_eq, mem_diff]
    have hcα : Real.cos (π - α) = -(r / 2) := by rw [Real.cos_pi_sub, hcos]
    constructor
    · rintro ⟨ht, h⟩
      refine ⟨ht, (cos_pi_sub_le_iff ht hα0.le (by linarith)).mp ?_⟩
      rw [hcα]; nlinarith
    · rintro ⟨ht, h⟩
      refine ⟨ht, ?_⟩
      have := (cos_pi_sub_le_iff ht hα0.le (by linarith)).mpr h
      rw [hcα] at this; nlinarith
  -- the integrals
  unfold greenArea
  rw [Fin.sum_univ_two, e0, e1]
  simp only [two_zero, two_one, zero_mul, add_zero]
  have i0 : ∫ t in Icc α (2 * π - α), (1 : ℝ) = 2 * π - 2 * α := by
    rw [setIntegral_const, smul_eq_mul, mul_one, Real.volume_real_Icc_of_le (by linarith)]; ring
  have hsub : Ioo (π - α) (π + α) ⊆ Ico 0 (2 * π) := fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hint : IntegrableOn (fun t => 1 + r * Real.cos t) (Ico 0 (2 * π)) :=
    (continuous_const.add (Real.continuous_cos.const_mul r)).integrableOn_Icc.mono_set Ico_subset_Icc_self
  have i1 : ∫ t in Ico 0 (2 * π) \ Ioo (π - α) (π + α), (1 + r * Real.cos t)
      = 2 * π - 2 * α + 2 * r * Real.sin α := by
    rw [integral_diff measurableSet_Ioo hint hsub, setIntegral_Ico' (by linarith),
      setIntegral_Ioo' (by linarith), integral_one_add_mul_cos, integral_one_add_mul_cos,
      Real.sin_two_pi, Real.sin_zero, Real.sin_add, Real.sin_sub, Real.sin_pi, Real.cos_pi]
    ring
  rw [i0, i1, hsin]
  ring

/-- `greenArea` of two unit disks at distance `r ≥ 2` -/
theorem greenArea_two_far {r : ℝ} (hr : 2 ≤ r) : greenArea (two r) = 2 * π := by
  have hπ := Real.pi_pos
  have e0 : exposed (two r) 0 = Ico 0 (2 * π) := by
    rw [exposed_two_zero]
    ext t
    simp only [Set.mem_setOf_eq, and_iff_left_iff_imp]
    intro _
    have := Real.cos_le_one t
    nlinarith
  have e1 : exposed (two r) 1 = Ico 0 (2 * π) := by
    rw [exposed_two_one]
    ext t
    simp only [Set.mem_setOf_eq, and_iff_left_iff_imp]
    intro _
    have := Real.neg_one_le_cos t
    nlinarith
  unfold greenArea
  rw [Fin.sum_univ_two, e0, e1]
  simp only [two_zero, two_one, zero_mul, add_zero]
  rw [setIntegral_Ico' (by linarith), setIntegral_Ico' (by linarith), integral_one_add_mul_cos]
  simp only [intervalIntegral.integral_const, smul_eq_mul, mul_one, Real.sin_two_pi, Real.sin_zero]
  ring

/-- Two unit disks at distance `r ∈ (0, 2)` (under Green's formula): `A = 2π - 2 arccos(r/2) + (r/2)√(4 - r²)`. -/
theorem unionArea_two (hG : GreenFormula) {r : ℝ} (hr0 : 0 < r) (hr2 : r < 2) :
    unionArea (two r) = 2 * π - 2 * Real.arccos (r / 2) + r / 2 * √(4 - r ^ 2) := by
  rw [hG 2 (two r) (two_ne r hr0.ne'), greenArea_two hr0 hr2]

/-- Two unit disks at distance `r ≥ 2` (under Green's formula): `A = 2π`. -/
theorem unionArea_two_far (hG : GreenFormula) {r : ℝ} (hr : 2 ≤ r) : unionArea (two r) = 2 * π := by
  rw [hG 2 (two r) (two_ne r (by linarith)), greenArea_two_far hr]

end TD

end

end BHH
