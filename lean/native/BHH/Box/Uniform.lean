/-
Module C infrastructure: the uniform probability measure on an interval and on a closed box, its relation to the
volume, independence of the coordinates, and the moments of a centred uniform variable.
-/
import BHH.Interfaces

open MeasureTheory Set Real ProbabilityTheory
open scoped ENNReal

noncomputable section

namespace BHH

/-! ## The uniform measure on an interval -/

/-- the uniform probability measure on `[a, b]` (for `a < b`) -/
def unifI (a b : ℝ) : Measure ℝ := (ENNReal.ofReal (b - a))⁻¹ • volume.restrict (Icc a b)

lemma ofReal_sub_ne_zero {a b : ℝ} (h : a < b) : ENNReal.ofReal (b - a) ≠ 0 :=
  (ENNReal.ofReal_pos.2 (sub_pos.2 h)).ne'

lemma unifI_univ {a b : ℝ} (h : a < b) : unifI a b univ = 1 := by
  rw [unifI, Measure.smul_apply, Measure.restrict_apply MeasurableSet.univ, univ_inter, Real.volume_Icc,
    smul_eq_mul]
  exact ENNReal.inv_mul_cancel (ofReal_sub_ne_zero h) ENNReal.ofReal_ne_top

lemma unifI_isProb {a b : ℝ} (h : a < b) : IsProbabilityMeasure (unifI a b) := ⟨unifI_univ h⟩

lemma restrict_Icc_eq_smul_unifI {a b : ℝ} (h : a < b) :
    volume.restrict (Icc a b) = ENNReal.ofReal (b - a) • unifI a b := by
  rw [unifI, smul_smul, ENNReal.mul_inv_cancel (ofReal_sub_ne_zero h) ENNReal.ofReal_ne_top, one_smul]

lemma integral_unifI {a b : ℝ} (h : a < b) (g : ℝ → ℝ) :
    ∫ t, g t ∂unifI a b = (b - a)⁻¹ * ∫ t in a..b, g t := by
  rw [unifI, integral_smul_measure, intervalIntegral.integral_of_le h.le, ← integral_Icc_eq_integral_Ioc,
    smul_eq_mul, ENNReal.toReal_inv, ENNReal.toReal_ofReal (sub_nonneg.2 h.le)]

lemma unifI_ae_mem {a b : ℝ} : ∀ᵐ t ∂unifI a b, t ∈ Icc a b :=
  Measure.ae_smul_measure (ae_restrict_mem measurableSet_Icc) _

/-- `∫ (t - (a+b)/2)^n` over the uniform measure on `[a, b]` -/
lemma integral_unifI_mid_pow {a b : ℝ} (h : a < b) (n : ℕ) :
    ∫ t, (t - (a + b) / 2) ^ n ∂unifI a b =
      (b - a)⁻¹ * ((((b - a) / 2) ^ (n + 1) - (-((b - a) / 2)) ^ (n + 1)) / (n + 1)) := by
  rw [integral_unifI h, intervalIntegral.integral_comp_sub_right (fun t => t ^ n), integral_pow]
  congr 3 <;> ring

lemma integral_unifI_mid {a b : ℝ} (h : a < b) : ∫ t, (t - (a + b) / 2) ∂unifI a b = 0 := by
  have := integral_unifI_mid_pow h 1
  simp only [pow_one] at this
  rw [this]; ring

lemma integral_unifI_mid_sq {a b : ℝ} (h : a < b) :
    ∫ t, (t - (a + b) / 2) ^ 2 ∂unifI a b = (b - a) ^ 2 / 12 := by
  rw [integral_unifI_mid_pow h 2]
  have hba : b - a ≠ 0 := (sub_pos.2 h).ne'
  field_simp
  ring

lemma integral_unifI_mid_four {a b : ℝ} (h : a < b) :
    ∫ t, (t - (a + b) / 2) ^ 4 ∂unifI a b = (b - a) ^ 4 / 80 := by
  rw [integral_unifI_mid_pow h 4]
  have hba : b - a ≠ 0 := (sub_pos.2 h).ne'
  field_simp
  ring

/-! ## The uniform measure on a closed box -/

/-- the uniform probability measure on the closed box `rbox lo hi` -/
def unifBox {m : ℕ} (lo hi : Fin m → ℝ) : Measure (Fin m → ℝ) := Measure.pi fun d => unifI (lo d) (hi d)

variable {m : ℕ} {lo hi : Fin m → ℝ}

lemma unifBox_isProb (h : ∀ d, lo d < hi d) : IsProbabilityMeasure (unifBox lo hi) := by
  have : ∀ d, IsProbabilityMeasure (unifI (lo d) (hi d)) := fun d => unifI_isProb (h d)
  unfold unifBox; infer_instance

lemma measurableSet_rbox : MeasurableSet (rbox lo hi) :=
  MeasurableSet.univ_pi fun _ => measurableSet_Icc

lemma volume_rbox :
    volume (rbox lo hi) = ∏ d, ENNReal.ofReal (hi d - lo d) := by
  rw [rbox, volume_pi, Measure.pi_pi]
  simp only [Real.volume_Icc]

lemma volume_rbox_toReal (h : ∀ d, lo d ≤ hi d) :
    (volume (rbox lo hi)).toReal = ∏ d, (hi d - lo d) := by
  rw [volume_rbox, ENNReal.toReal_prod]
  exact Finset.prod_congr rfl fun d _ => ENNReal.toReal_ofReal (sub_nonneg.2 (h d))

lemma volume_rbox_ne_zero (h : ∀ d, lo d < hi d) : volume (rbox lo hi) ≠ 0 := by
  rw [volume_rbox]
  exact Finset.prod_ne_zero_iff.2 fun d _ => ofReal_sub_ne_zero (h d)

lemma volume_rbox_ne_top : volume (rbox lo hi) ≠ ⊤ := by
  rw [volume_rbox]
  exact ENNReal.prod_ne_top fun d _ => ENNReal.ofReal_ne_top

lemma volume_rbox_toReal_pos (h : ∀ d, lo d < hi d) : 0 < (volume (rbox lo hi)).toReal :=
  ENNReal.toReal_pos (volume_rbox_ne_zero h) volume_rbox_ne_top

/-- the volume restricted to the box is `vol(box)` times the uniform measure -/
lemma restrict_rbox (h : ∀ d, lo d < hi d) :
    volume.restrict (rbox lo hi) = volume (rbox lo hi) • unifBox lo hi := by
  have : ∀ d, IsProbabilityMeasure (unifI (lo d) (hi d)) := fun d => unifI_isProb (h d)
  rw [volume_rbox, rbox, volume_pi, Measure.restrict_pi_pi]
  refine Measure.pi_eq fun s hs => ?_
  rw [Measure.smul_apply, unifBox, Measure.pi_pi, smul_eq_mul, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun d _ => ?_
  rw [restrict_Icc_eq_smul_unifI (h d), Measure.smul_apply, smul_eq_mul]

lemma unifBox_eq (h : ∀ d, lo d < hi d) :
    unifBox lo hi = (volume (rbox lo hi))⁻¹ • volume.restrict (rbox lo hi) := by
  rw [restrict_rbox h, smul_smul, ENNReal.inv_mul_cancel (volume_rbox_ne_zero h)
    volume_rbox_ne_top, one_smul]

lemma unifBox_ae_mem (h : ∀ d, lo d < hi d) : ∀ᵐ x ∂unifBox lo hi, x ∈ rbox lo hi := by
  rw [unifBox_eq h]
  exact Measure.ae_smul_measure (ae_restrict_mem measurableSet_rbox) _

lemma setIntegral_rbox (h : ∀ d, lo d < hi d) (g : (Fin m → ℝ) → ℝ) :
    ∫ x in rbox lo hi, g x = (volume (rbox lo hi)).toReal * ∫ x, g x ∂unifBox lo hi := by
  rw [restrict_rbox h, integral_smul_measure, smul_eq_mul]

lemma setLIntegral_rbox (h : ∀ d, lo d < hi d) (g : (Fin m → ℝ) → ℝ≥0∞) :
    ∫⁻ x in rbox lo hi, g x = volume (rbox lo hi) * ∫⁻ x, g x ∂unifBox lo hi := by
  rw [restrict_rbox h, lintegral_smul_measure, smul_eq_mul]

/-- the coordinates are independent under the uniform measure on the box -/
lemma unifBox_iIndep (h : ∀ d, lo d < hi d) :
    iIndepFun (fun d (x : Fin m → ℝ) => x d) (unifBox lo hi) := by
  have : ∀ d, IsProbabilityMeasure (unifI (lo d) (hi d)) := fun d => unifI_isProb (h d)
  exact iIndepFun_pi (X := fun _ => id) fun _ => aemeasurable_id

lemma unifBox_map_eval (h : ∀ d, lo d < hi d) (d : Fin m) :
    (unifBox lo hi).map (fun x => x d) = unifI (lo d) (hi d) := by
  have : ∀ d, IsProbabilityMeasure (unifI (lo d) (hi d)) := fun d => unifI_isProb (h d)
  exact (measurePreserving_eval _ d).map_eq

lemma integral_unifBox_coord (h : ∀ d, lo d < hi d) (d : Fin m) (g : ℝ → ℝ) (hg : Measurable g) :
    ∫ x, g (x d) ∂unifBox lo hi = ∫ t, g t ∂unifI (lo d) (hi d) := by
  rw [← unifBox_map_eval h d, integral_map (measurable_pi_apply d).aemeasurable
    hg.aestronglyMeasurable]

/-- centred coordinate `x_d - c_d` -/
lemma integral_unifBox_mid (h : ∀ d, lo d < hi d) (d : Fin m) :
    ∫ x, (x d - (lo d + hi d) / 2) ∂unifBox lo hi = 0 := by
  rw [integral_unifBox_coord h d (fun t => t - (lo d + hi d) / 2) (by fun_prop)]
  exact integral_unifI_mid (h d)

lemma integral_unifBox_mid_sq (h : ∀ d, lo d < hi d) (d : Fin m) :
    ∫ x, (x d - (lo d + hi d) / 2) ^ 2 ∂unifBox lo hi = (hi d - lo d) ^ 2 / 12 := by
  rw [integral_unifBox_coord h d (fun t => (t - (lo d + hi d) / 2) ^ 2) (by fun_prop)]
  exact integral_unifI_mid_sq (h d)

lemma integral_unifBox_mid_four (h : ∀ d, lo d < hi d) (d : Fin m) :
    ∫ x, (x d - (lo d + hi d) / 2) ^ 4 ∂unifBox lo hi = (hi d - lo d) ^ 4 / 80 := by
  rw [integral_unifBox_coord h d (fun t => (t - (lo d + hi d) / 2) ^ 4) (by fun_prop)]
  exact integral_unifI_mid_four (h d)

/-- `E[(x_d - c_d)(x_e - c_e)] = 0` for `d ≠ e` -/
lemma integral_unifBox_mid_mul (h : ∀ d, lo d < hi d) {d e : Fin m} (hde : d ≠ e) :
    ∫ x, (x d - (lo d + hi d) / 2) * (x e - (lo e + hi e) / 2) ∂unifBox lo hi = 0 := by
  have hind := (unifBox_iIndep h).indepFun hde
  have h2 : IndepFun (fun x : Fin m → ℝ => x d - (lo d + hi d) / 2)
      (fun x : Fin m → ℝ => x e - (lo e + hi e) / 2) (unifBox lo hi) :=
    hind.comp (φ := fun t => t - (lo d + hi d) / 2) (ψ := fun t => t - (lo e + hi e) / 2)
      (by fun_prop) (by fun_prop)
  rw [h2.integral_fun_mul_eq_mul_integral ((measurable_pi_apply d).sub_const _).aestronglyMeasurable
    ((measurable_pi_apply e).sub_const _).aestronglyMeasurable]
  simp only [integral_unifBox_mid h d, zero_mul]

end BHH
