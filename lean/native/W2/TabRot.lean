/-
T7: `RotA2`: rotating both sectors of a pair by `φ` keeps the integral of `A_2`
(`rotL φ` maps sectors to rotated sectors, preserves `A_2`, and `(w, z) ↦ (R w, R z)` preserves the product measure).
-/
import W2.TabProps
import W2.GeoRot

open MeasureTheory Set Real
open scoped ENNReal

noncomputable section

namespace BHH.W2

open BHH

lemma rotL_polar (φ ρ θ : ℝ) : rotL φ (polarCoord.symm (ρ, θ)) = polarCoord.symm (ρ, θ + φ) := by
  rw [rotL_apply, polarCoord_symm_apply, polarCoord_symm_apply, Real.cos_add, Real.sin_add]
  ext <;> simp only <;> ring

lemma rotL_image_sector (φ r1 r2 a b : ℝ) : rotL φ '' sector r1 r2 a b = sector r1 r2 (a + φ) (b + φ) := by
  ext x
  constructor
  · rintro ⟨_, ⟨⟨ρ, θ⟩, ⟨hρ, hθ⟩, rfl⟩, rfl⟩
    refine ⟨(ρ, θ + φ), ⟨hρ, ?_⟩, (rotL_polar φ ρ θ).symm⟩
    simp only [mem_Ioo] at hθ ⊢
    constructor <;> linarith [hθ.1, hθ.2]
  · rintro ⟨⟨ρ, θ'⟩, ⟨hρ, hθ⟩, rfl⟩
    refine ⟨polarCoord.symm (ρ, θ' - φ), ⟨(ρ, θ' - φ), ⟨hρ, ?_⟩, rfl⟩, ?_⟩
    · simp only [mem_Ioo] at hθ ⊢
      constructor <;> linarith [hθ.1, hθ.2]
    · rw [rotL_polar, sub_add_cancel]

lemma A2_rotL (φ : ℝ) (w z : Pt) : A2 (rotL φ w) (rotL φ z) = A2 w z := by
  unfold A2
  have hpre : rotL φ ⁻¹' (disk (rotL φ z) 1 \ (disk 0 1 ∪ disk (-rotL φ w) 1)) =
      disk z 1 \ (disk 0 1 ∪ disk (-w) 1) := by
    ext x
    have e0 : sqDist (rotL φ x) 0 = sqDist x 0 := by
      have := sqDist_rotL φ x 0
      rwa [map_zero] at this
    have e1 : sqDist (rotL φ x) (-rotL φ w) = sqDist x (-w) := by
      rw [show -rotL φ w = rotL φ (-w) from (map_neg _ _).symm, sqDist_rotL]
    simp only [mem_preimage, mem_sdiff, mem_union, disk, mem_ofPred_eq, sqDist_rotL, e0, e1]
  have hm : MeasurableSet (disk (rotL φ z) 1 \ (disk 0 1 ∪ disk (-rotL φ w) 1)) :=
    (measurableSet_disk _ _).diff ((measurableSet_disk _ _).union (measurableSet_disk _ _))
  rw [← hpre, (mp_rotL φ).measure_preimage hm.nullMeasurableSet]

/-- `rotL φ` as a measurable equivalence -/
def rotE (φ : ℝ) : Pt ≃ᵐ Pt :=
  (LinearMap.equivOfDetNeZero (rotL φ) (by rw [det_rotL]; exact one_ne_zero)).toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv

lemma rotE_coe (φ : ℝ) : ⇑(rotE φ) = rotL φ := rfl

theorem rotA2 : RotA2 := by
  intro r1 r2 a b q1 q2 a' b' φ _ _ _ _ _ _ _ _ _ _
  set T : Pt × Pt → Pt × Pt := fun p => (rotL φ p.1, rotL φ p.2) with hT
  have hTmp : MeasurePreserving T volume volume := by
    have h := (mp_rotL φ).prod (mp_rotL φ)
    rw [← Measure.volume_eq_prod (α := Pt) (β := Pt)] at h
    exact h
  have hTemb : MeasurableEmbedding T := by
    have := ((rotE φ).prodCongr (rotE φ)).measurableEmbedding
    exact this
  have himg : T '' (sector r1 r2 a b ×ˢ sector q1 q2 a' b') =
      sector r1 r2 (a + φ) (b + φ) ×ˢ sector q1 q2 (a' + φ) (b' + φ) := by
    rw [hT, ← prod_image_image_eq, rotL_image_sector, rotL_image_sector]
  rw [← himg, hTmp.setIntegral_image_emb hTemb]
  simp only [hT, A2_rotL]

end BHH.W2
