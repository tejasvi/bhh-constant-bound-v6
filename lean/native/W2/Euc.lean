/-
Euclidean norm and distance on `Pt = ℝ × ℝ` (`enorm2`, `edist2` of `BHH/Defs.lean`), through `ℂ`.
-/
import BHH.Defs

open Real

namespace BHH.W2

open BHH

/-- the point as a complex number -/
noncomputable def toC (u : Pt) : ℂ := Complex.equivRealProd.symm u

lemma toC_add (u v : Pt) : toC (u + v) = toC u + toC v := by
  unfold toC; apply Complex.ext <;> simp

lemma toC_sub (u v : Pt) : toC (u - v) = toC u - toC v := by
  unfold toC; apply Complex.ext <;> simp

lemma toC_neg (u : Pt) : toC (-u) = -toC u := by
  unfold toC; apply Complex.ext <;> simp

lemma toC_smul (t : ℝ) (u : Pt) : toC (t • u) = (t : ℂ) * toC u := by
  unfold toC; apply Complex.ext <;> simp

lemma enorm2_eq_norm (u : Pt) : enorm2 u = ‖toC u‖ := by
  unfold enorm2 toC
  rw [Complex.norm_def, Complex.normSq_apply]
  simp only [Complex.equivRealProd_symm_apply, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
    Complex.I_re, Complex.ofReal_im, Complex.I_im, Complex.add_im, Complex.mul_im]
  congr 1; ring

lemma edist2_eq (a b : Pt) : edist2 a b = enorm2 (a - b) := by
  unfold edist2 enorm2 sqDist; rfl

lemma edist2_eq_norm (a b : Pt) : edist2 a b = ‖toC a - toC b‖ := by
  rw [edist2_eq, enorm2_eq_norm, toC_sub]

lemma enorm2_nonneg (u : Pt) : 0 ≤ enorm2 u := Real.sqrt_nonneg _

lemma edist2_nonneg (a b : Pt) : 0 ≤ edist2 a b := Real.sqrt_nonneg _

lemma enorm2_add_le (u v : Pt) : enorm2 (u + v) ≤ enorm2 u + enorm2 v := by
  rw [enorm2_eq_norm, enorm2_eq_norm, enorm2_eq_norm, toC_add]; exact norm_add_le _ _

lemma enorm2_neg (u : Pt) : enorm2 (-u) = enorm2 u := by
  rw [enorm2_eq_norm, enorm2_eq_norm, toC_neg, norm_neg]

lemma enorm2_smul (t : ℝ) (u : Pt) : enorm2 (t • u) = |t| * enorm2 u := by
  rw [enorm2_eq_norm, enorm2_eq_norm, toC_smul, norm_mul, Complex.norm_real, Real.norm_eq_abs]

lemma edist2_comm (a b : Pt) : edist2 a b = edist2 b a := by
  rw [edist2_eq_norm, edist2_eq_norm, norm_sub_rev]

lemma edist2_triangle (a b c : Pt) : edist2 a c ≤ edist2 a b + edist2 b c := by
  rw [edist2_eq_norm, edist2_eq_norm, edist2_eq_norm]; exact norm_sub_le_norm_sub_add_norm_sub _ _ _

lemma abs_enorm2_sub_le (u v : Pt) : |enorm2 u - enorm2 v| ≤ enorm2 (u - v) := by
  rw [enorm2_eq_norm, enorm2_eq_norm, enorm2_eq_norm, toC_sub]; exact abs_norm_sub_norm_le _ _

lemma enorm2_polar (ρ φ : ℝ) (hρ : 0 ≤ ρ) : enorm2 (ρ * Real.cos φ, ρ * Real.sin φ) = ρ := by
  unfold enorm2
  rw [show (ρ * Real.cos φ) ^ 2 + (ρ * Real.sin φ) ^ 2 = ρ ^ 2 by
    linear_combination ρ ^ 2 * Real.cos_sq_add_sin_sq φ]
  exact Real.sqrt_sq hρ

lemma edist2_zero_right (u : Pt) : edist2 u 0 = enorm2 u := by
  rw [edist2_eq, sub_zero]

lemma sqDist_add_zero (w z : Pt) : sqDist (w + z) 0 = enorm2 (w + z) ^ 2 := by
  unfold enorm2 sqDist
  rw [Real.sq_sqrt (by positivity)]
  simp

/-- `|ρ u(φ) + ρ' u(φ')|² = ρ² + ρ'² + 2 ρ ρ' cos(φ' - φ)`. -/
lemma enorm2_polar_add_sq (ρ φ ρ' φ' : ℝ) :
    enorm2 ((ρ * Real.cos φ, ρ * Real.sin φ) + (ρ' * Real.cos φ', ρ' * Real.sin φ')) ^ 2 =
      ρ ^ 2 + ρ' ^ 2 + 2 * ρ * ρ' * Real.cos (φ' - φ) := by
  unfold enorm2
  rw [Real.sq_sqrt (by positivity), Real.cos_sub]
  simp only [Prod.fst_add, Prod.snd_add]
  linear_combination ρ ^ 2 * Real.cos_sq_add_sin_sq φ + ρ' ^ 2 * Real.cos_sq_add_sin_sq φ'

end BHH.W2
