/-
Module G: integrals over polar cells `polarCoord.symm '' (Ioo r₁ r₂ ×ˢ Ioo θ₁ θ₂)`:
the change of variables, Fubini on the box, area, first and second moments, radial integrals.
-/
import W2.DiscCells

open MeasureTheory Set Real
open scoped ENNReal

noncomputable section

namespace BHH.W2

/-- the open polar cell with radii `(r₁, r₂)` and angles `(θ₁, θ₂)` -/
def pcell (r₁ r₂ θ₁ θ₂ : ℝ) : Set Pt := polarCoord.symm '' (Ioo r₁ r₂ ×ˢ Ioo θ₁ θ₂)

variable {r₁ r₂ θ₁ θ₂ : ℝ}

lemma box_subset_target (hr : 0 ≤ r₁) (hθ₁ : -π ≤ θ₁) (hθ₂ : θ₂ ≤ π) :
    Ioo r₁ r₂ ×ˢ Ioo θ₁ θ₂ ⊆ polarCoord.target := by
  intro p hp
  simp only [mem_prod, mem_Ioo] at hp
  simp only [polarCoord_target, mem_prod, mem_Ioi, mem_Ioo]
  exact ⟨hr.trans_lt hp.1.1, by linarith [hp.2.1], by linarith [hp.2.2]⟩

lemma isOpen_box : IsOpen (Ioo r₁ r₂ ×ˢ Ioo θ₁ θ₂) := isOpen_Ioo.prod isOpen_Ioo

lemma isOpen_pcell (hr : 0 ≤ r₁) (hθ₁ : -π ≤ θ₁) (hθ₂ : θ₂ ≤ π) : IsOpen (pcell r₁ r₂ θ₁ θ₂) :=
  polarCoord.isOpen_image_symm_of_subset_target isOpen_box (box_subset_target hr hθ₁ hθ₂)

lemma measurableSet_pcell (hr : 0 ≤ r₁) (hθ₁ : -π ≤ θ₁) (hθ₂ : θ₂ ≤ π) :
    MeasurableSet (pcell r₁ r₂ θ₁ θ₂) := (isOpen_pcell hr hθ₁ hθ₂).measurableSet

/-- change of variables on the image of an open subset of the polar target -/
lemma setIntegral_polar_image {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {S : Set (ℝ × ℝ)}
    (hSo : IsOpen S) (hS : S ⊆ polarCoord.target) (g : Pt → E) :
    ∫ z in polarCoord.symm '' S, g z = ∫ p in S, p.1 • g (polarCoord.symm p) := by
  have hm : MeasurableSet (polarCoord.symm '' S) :=
    (polarCoord.isOpen_image_symm_of_subset_target hSo hS).measurableSet
  rw [← integral_indicator hm, ← integral_comp_polarCoord_symm, ← integral_indicator hSo.measurableSet,
    ← setIntegral_eq_integral_of_forall_compl_eq_zero (s := polarCoord.target)
      (fun p hp => indicator_of_notMem (fun h => hp (hS h)) _)]
  refine setIntegral_congr_fun polarCoord.open_target.measurableSet fun p hp => ?_
  by_cases hpS : p ∈ S
  · simp only [indicator_of_mem hpS, indicator_of_mem (mem_image_of_mem _ hpS)]
  · have hnot : polarCoord.symm p ∉ polarCoord.symm '' S := by
      rintro ⟨q, hq, he⟩
      have hp' : p ∈ polarCoord.symm.source := by rw [polarCoord.symm_source]; exact hp
      have hq' : q ∈ polarCoord.symm.source := by rw [polarCoord.symm_source]; exact hS hq
      exact hpS (polarCoord.symm.injOn hq' hp' he ▸ hq)
    simp only [indicator_of_notMem hpS, indicator_of_notMem hnot, smul_zero]

lemma setIntegral_pcell {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (hr : 0 ≤ r₁) (hθ₁ : -π ≤ θ₁)
    (hθ₂ : θ₂ ≤ π) (g : Pt → E) :
    ∫ z in pcell r₁ r₂ θ₁ θ₂, g z = ∫ p in Ioo r₁ r₂ ×ˢ Ioo θ₁ θ₂, p.1 • g (polarCoord.symm p) :=
  setIntegral_polar_image isOpen_box (box_subset_target hr hθ₁ hθ₂) g

/-- Fubini on the box for products -/
lemma setIntegral_box_mul (h12 : r₁ ≤ r₂) (hθ : θ₁ ≤ θ₂) (F G : ℝ → ℝ) :
    ∫ p in Ioo r₁ r₂ ×ˢ Ioo θ₁ θ₂, F p.1 * G p.2 = (∫ r in r₁..r₂, F r) * ∫ θ in θ₁..θ₂, G θ := by
  rw [Measure.volume_eq_prod, setIntegral_prod_mul, intervalIntegral.integral_of_le h12,
    intervalIntegral.integral_of_le hθ, integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]

lemma setIntegral_box_fst (h12 : r₁ ≤ r₂) (hθ : θ₁ ≤ θ₂) (F : ℝ → ℝ) :
    ∫ p in Ioo r₁ r₂ ×ˢ Ioo θ₁ θ₂, F p.1 = (∫ r in r₁..r₂, F r) * (θ₂ - θ₁) := by
  have h := setIntegral_box_mul h12 hθ F (fun _ => (1 : ℝ))
  simp only [mul_one, intervalIntegral.integral_const, smul_eq_mul] at h
  exact h

lemma integrableOn_box {F G : ℝ → ℝ} (hF : Continuous F) (hG : Continuous G) :
    IntegrableOn (fun p : ℝ × ℝ => F p.1 * G p.2) (Ioo r₁ r₂ ×ˢ Ioo θ₁ θ₂) :=
  (ContinuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
    ((hF.comp continuous_fst).mul (hG.comp continuous_snd)).continuousOn).mono_set
    (prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self)

lemma integrableOn_box_fst {F : ℝ → ℝ} (hF : Continuous F) :
    IntegrableOn (fun p : ℝ × ℝ => F p.1) (Ioo r₁ r₂ ×ˢ Ioo θ₁ θ₂) :=
  (ContinuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
    (hF.comp continuous_fst).continuousOn).mono_set (prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self)

lemma polar_symm_fst (p : ℝ × ℝ) : (polarCoord.symm p).1 = p.1 * Real.cos p.2 := by
  simp [polarCoord_symm_apply]

lemma polar_symm_snd (p : ℝ × ℝ) : (polarCoord.symm p).2 = p.1 * Real.sin p.2 := by
  simp [polarCoord_symm_apply]

lemma box_pow_cos (h12 : r₁ ≤ r₂) (hθ : θ₁ ≤ θ₂) (n : ℕ) :
    ∫ p in Ioo r₁ r₂ ×ˢ Ioo θ₁ θ₂, p.1 ^ n * Real.cos p.2 =
      (r₂ ^ (n + 1) - r₁ ^ (n + 1)) / (n + 1) * (Real.sin θ₂ - Real.sin θ₁) :=
  (setIntegral_box_mul h12 hθ (fun r => r ^ n) Real.cos).trans (by simp only [integral_pow, integral_cos])

lemma box_pow_sin (h12 : r₁ ≤ r₂) (hθ : θ₁ ≤ θ₂) (n : ℕ) :
    ∫ p in Ioo r₁ r₂ ×ˢ Ioo θ₁ θ₂, p.1 ^ n * Real.sin p.2 =
      (r₂ ^ (n + 1) - r₁ ^ (n + 1)) / (n + 1) * (Real.cos θ₁ - Real.cos θ₂) :=
  (setIntegral_box_mul h12 hθ (fun r => r ^ n) Real.sin).trans (by simp only [integral_pow, integral_sin])

lemma box_pow (h12 : r₁ ≤ r₂) (hθ : θ₁ ≤ θ₂) (n : ℕ) :
    ∫ p in Ioo r₁ r₂ ×ˢ Ioo θ₁ θ₂, p.1 ^ n = (r₂ ^ (n + 1) - r₁ ^ (n + 1)) / (n + 1) * (θ₂ - θ₁) :=
  (setIntegral_box_fst h12 hθ (fun r => r ^ n)).trans (by simp only [integral_pow])

section formulas

variable (hr : 0 ≤ r₁) (h12 : r₁ ≤ r₂) (hθ₁ : -π ≤ θ₁) (hθ : θ₁ ≤ θ₂) (hθ₂ : θ₂ ≤ π)
include hr h12 hθ₁ hθ hθ₂

lemma area_pcell : (volume (pcell r₁ r₂ θ₁ θ₂)).toReal = (r₂ ^ 2 - r₁ ^ 2) / 2 * (θ₂ - θ₁) := by
  have h := setIntegral_pcell (r₂ := r₂) hr hθ₁ hθ₂ (fun _ => (1 : ℝ))
  rw [setIntegral_const, measureReal_def, smul_eq_mul, mul_one] at h
  rw [h]
  have e : ∀ p : ℝ × ℝ, p.1 • (1 : ℝ) = p.1 ^ 1 := fun p => by simp
  simp_rw [e]
  rw [box_pow h12 hθ 1]
  norm_num

lemma integral_pcell_fst :
    ∫ z in pcell r₁ r₂ θ₁ θ₂, z.1 = (r₂ ^ 3 - r₁ ^ 3) / 3 * (Real.sin θ₂ - Real.sin θ₁) := by
  rw [setIntegral_pcell hr hθ₁ hθ₂]
  have e : ∀ p : ℝ × ℝ, p.1 • (polarCoord.symm p).1 = p.1 ^ 2 * Real.cos p.2 := fun p => by
    rw [polar_symm_fst, smul_eq_mul]; ring
  simp_rw [e]
  rw [box_pow_cos h12 hθ 2]
  norm_num

lemma integral_pcell_snd :
    ∫ z in pcell r₁ r₂ θ₁ θ₂, z.2 = (r₂ ^ 3 - r₁ ^ 3) / 3 * (Real.cos θ₁ - Real.cos θ₂) := by
  rw [setIntegral_pcell hr hθ₁ hθ₂]
  have e : ∀ p : ℝ × ℝ, p.1 • (polarCoord.symm p).2 = p.1 ^ 2 * Real.sin p.2 := fun p => by
    rw [polar_symm_snd, smul_eq_mul]; ring
  simp_rw [e]
  rw [box_pow_sin h12 hθ 2]
  norm_num

lemma integral_pcell_sq :
    ∫ z in pcell r₁ r₂ θ₁ θ₂, (z.1 ^ 2 + z.2 ^ 2) = (r₂ ^ 4 - r₁ ^ 4) / 4 * (θ₂ - θ₁) := by
  rw [setIntegral_pcell hr hθ₁ hθ₂]
  have e : ∀ p : ℝ × ℝ, p.1 • ((polarCoord.symm p).1 ^ 2 + (polarCoord.symm p).2 ^ 2) = p.1 ^ 3 := fun p => by
    rw [polar_symm_fst, polar_symm_snd, smul_eq_mul]
    have := Real.cos_sq_add_sin_sq p.2
    linear_combination p.1 ^ 3 * this
  simp_rw [e]
  rw [box_pow h12 hθ 3]
  norm_num

/-- the second moment about a point `c` -/
lemma integral_pcell_sqDist (c : Pt) :
    ∫ z in pcell r₁ r₂ θ₁ θ₂, sqDist z c =
      (r₂ ^ 4 - r₁ ^ 4) / 4 * (θ₂ - θ₁) - 2 * c.1 * ((r₂ ^ 3 - r₁ ^ 3) / 3 * (Real.sin θ₂ - Real.sin θ₁)) -
        2 * c.2 * ((r₂ ^ 3 - r₁ ^ 3) / 3 * (Real.cos θ₁ - Real.cos θ₂)) +
        (c.1 ^ 2 + c.2 ^ 2) * ((r₂ ^ 2 - r₁ ^ 2) / 2 * (θ₂ - θ₁)) := by
  rw [setIntegral_pcell hr hθ₁ hθ₂]
  have e : ∀ p : ℝ × ℝ, p.1 • sqDist (polarCoord.symm p) c =
      p.1 ^ 3 - 2 * c.1 * (p.1 ^ 2 * Real.cos p.2) - 2 * c.2 * (p.1 ^ 2 * Real.sin p.2) +
        (c.1 ^ 2 + c.2 ^ 2) * p.1 ^ 1 := fun p => by
    rw [sqDist, polar_symm_fst, polar_symm_snd, smul_eq_mul]
    have := Real.cos_sq_add_sin_sq p.2
    linear_combination p.1 ^ 3 * this
  simp_rw [e]
  have i1 : IntegrableOn (fun p : ℝ × ℝ => p.1 ^ 3) (Ioo r₁ r₂ ×ˢ Ioo θ₁ θ₂) :=
    integrableOn_box_fst (F := fun r => r ^ 3) (by fun_prop)
  have i2 : IntegrableOn (fun p : ℝ × ℝ => p.1 ^ 2 * Real.cos p.2) (Ioo r₁ r₂ ×ˢ Ioo θ₁ θ₂) :=
    integrableOn_box (F := fun r => r ^ 2) (G := Real.cos) (by fun_prop) (by fun_prop)
  have i3 : IntegrableOn (fun p : ℝ × ℝ => p.1 ^ 2 * Real.sin p.2) (Ioo r₁ r₂ ×ˢ Ioo θ₁ θ₂) :=
    integrableOn_box (F := fun r => r ^ 2) (G := Real.sin) (by fun_prop) (by fun_prop)
  have i4 : IntegrableOn (fun p : ℝ × ℝ => p.1 ^ 1) (Ioo r₁ r₂ ×ˢ Ioo θ₁ θ₂) :=
    integrableOn_box_fst (F := fun r => r ^ 1) (by fun_prop)
  have j1 : IntegrableOn (fun p : ℝ × ℝ => p.1 ^ 3 - 2 * c.1 * (p.1 ^ 2 * Real.cos p.2)) (Ioo r₁ r₂ ×ˢ Ioo θ₁ θ₂) :=
    i1.sub (i2.const_mul (2 * c.1))
  have j2 : IntegrableOn (fun p : ℝ × ℝ => p.1 ^ 3 - 2 * c.1 * (p.1 ^ 2 * Real.cos p.2) -
      2 * c.2 * (p.1 ^ 2 * Real.sin p.2)) (Ioo r₁ r₂ ×ˢ Ioo θ₁ θ₂) := j1.sub (i3.const_mul (2 * c.2))
  rw [integral_add j2 (i4.const_mul (c.1 ^ 2 + c.2 ^ 2)), integral_sub j1 (i3.const_mul (2 * c.2)),
    integral_sub i1 (i2.const_mul (2 * c.1)),
    integral_const_mul, integral_const_mul, integral_const_mul, box_pow h12 hθ 3,
    box_pow_cos h12 hθ 2, box_pow_sin h12 hθ 2, box_pow h12 hθ 1]
  norm_num

/-- radial functions -/
lemma integral_pcell_radial (f : ℝ → ℝ) :
    ∫ z in pcell r₁ r₂ θ₁ θ₂, f (Real.sqrt (z.1 ^ 2 + z.2 ^ 2)) = (∫ r in r₁..r₂, r * f r) * (θ₂ - θ₁) := by
  rw [setIntegral_pcell hr hθ₁ hθ₂]
  have e : EqOn (fun p : ℝ × ℝ => p.1 • f (Real.sqrt ((polarCoord.symm p).1 ^ 2 + (polarCoord.symm p).2 ^ 2)))
      (fun p : ℝ × ℝ => (fun r => r * f r) p.1) (Ioo r₁ r₂ ×ˢ Ioo θ₁ θ₂) := by
    intro p hp
    have hp1 : 0 < p.1 := hr.trans_lt hp.1.1
    have h : (polarCoord.symm p).1 ^ 2 + (polarCoord.symm p).2 ^ 2 = p.1 ^ 2 := by
      rw [polar_symm_fst, polar_symm_snd]
      have := Real.cos_sq_add_sin_sq p.2
      linear_combination p.1 ^ 2 * this
    simp only [h, Real.sqrt_sq hp1.le, smul_eq_mul]
  rw [setIntegral_congr_fun (isOpen_box.measurableSet) e]
  exact setIntegral_box_fst h12 hθ (fun r => r * f r)

end formulas

end BHH.W2
