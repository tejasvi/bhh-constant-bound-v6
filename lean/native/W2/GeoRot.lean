/-
Module G: rotation invariance of the union area: `A(R_φ y) = A(y)` for the rotation
`R_φ z = (cos φ z.1 - sin φ z.2, sin φ z.1 + cos φ z.2)` (a linear map of determinant 1 preserving `sqDist`), and
invariance under translations.
-/
import W2.LapPerm

open MeasureTheory Set Real
open scoped ENNReal

noncomputable section

namespace BHH.W2

open BHH

/-- the rotation by `φ`, as a linear map of `ℝ × ℝ` -/
def rotL (φ : ℝ) : Pt →ₗ[ℝ] Pt :=
  Matrix.toLin (Module.Basis.finTwoProd ℝ) (Module.Basis.finTwoProd ℝ) !![Real.cos φ, -Real.sin φ; Real.sin φ, Real.cos φ]

lemma rotL_apply (φ : ℝ) (z : Pt) :
    rotL φ z = (Real.cos φ * z.1 - Real.sin φ * z.2, Real.sin φ * z.1 + Real.cos φ * z.2) := by
  rw [rotL, Matrix.toLin_finTwoProd_apply]
  refine Prod.ext ?_ rfl
  simp only
  ring

lemma det_rotL (φ : ℝ) : LinearMap.det (rotL φ) = 1 := by
  rw [rotL, LinearMap.det_toLin, Matrix.det_fin_two_of]
  have := Real.cos_sq_add_sin_sq φ
  linear_combination this

lemma sqDist_rotL (φ : ℝ) (a b : Pt) : sqDist (rotL φ a) (rotL φ b) = sqDist a b := by
  rw [rotL_apply, rotL_apply, sqDist, sqDist]
  have := Real.cos_sq_add_sin_sq φ
  simp only
  linear_combination ((a.1 - b.1) ^ 2 + (a.2 - b.2) ^ 2) * this

lemma mp_rotL (φ : ℝ) : MeasurePreserving (rotL φ) volume volume := by
  have hne : LinearMap.det (rotL φ) ≠ 0 := by rw [det_rotL]; exact one_ne_zero
  refine ⟨(rotL φ).continuous_of_finiteDimensional.measurable, ?_⟩
  rw [Measure.map_linearMap_addHaar_eq_smul_addHaar volume hne, det_rotL, _root_.inv_one, abs_one, ENNReal.ofReal_one,
    one_smul]

lemma measurableSet_disk (a : Pt) (ρ : ℝ) : MeasurableSet (disk a ρ) :=
  measurableSet_le (by unfold sqDist; fun_prop) measurable_const

/-- rotation invariance of `unionArea` -/
theorem unionArea_rotL {k : ℕ} (φ : ℝ) (y : Fin k → Pt) : unionArea (fun i => rotL φ (y i)) = unionArea y := by
  unfold unionArea
  have hpre : rotL φ ⁻¹' (⋃ i, disk (rotL φ (y i)) 1) = ⋃ i, disk (y i) 1 := by
    ext z
    simp only [mem_preimage, mem_iUnion, disk, mem_ofPred_eq, sqDist_rotL]
  have hm : MeasurableSet (⋃ i, disk (rotL φ (y i)) 1) := MeasurableSet.iUnion fun i => measurableSet_disk _ _
  rw [← hpre, (mp_rotL φ).measure_preimage hm.nullMeasurableSet]

/-- translation invariance of `unionArea` -/
theorem unionArea_translate {k : ℕ} (c : Pt) (y : Fin k → Pt) : unionArea (fun i => y i + c) = unionArea y := by
  have := unionArea_relabel y (Equiv.refl _) (-c)
  simp only [Equiv.refl_apply, sub_neg_eq_add] at this
  exact this

end BHH.W2
