/-
T5: `A_1`, `A_2` through union areas: `A1Radial` (two disks: TwoDisk's `unionArea_two` under Green's
formula, after rotating `z` to `(|z|, 0)`), `A2Union` (`A_2(w, z) = A(-w, 0, z) - π - A_1(w)`, with `A_1(-w) = A_1(w)` by
the half-turn), `A2LeA1`.
-/
import W2.TabProps
import W2.GeoRot
import W2.TabPairAux
import BHH.TwoDisk

open MeasureTheory Set Real
open scoped ENNReal

noncomputable section

namespace BHH.W2

open BHH

lemma tp_volume_disk_ne_top (a : Pt) : volume (disk a 1) ≠ ⊤ := by
  rw [volume_disk_one]; exact ENNReal.ofReal_ne_top

/-- `|B \ A| = |A ∪ B| - |A|` for sets of finite measure -/
lemma tp_vol_diff_eq {A B : Set Pt} (hA : MeasurableSet A) (hB : MeasurableSet B) (hAf : volume A ≠ ⊤)
    (hBf : volume B ≠ ⊤) : (volume (B \ A)).toReal = (volume (A ∪ B)).toReal - (volume A).toReal := by
  have hU : A ∪ B = A ∪ (B \ A) := (union_sdiff_self).symm
  have h := measure_union (μ := volume) (disjoint_sdiff_right (s := A) (t := B)) (hB.diff hA)
  rw [← hU] at h
  have hdf : volume (B \ A) ≠ ⊤ := measure_ne_top_of_subset sdiff_subset hBf
  rw [h, ENNReal.toReal_add hAf hdf]
  ring

lemma tp_iUnion_two (a b : Pt) : (⋃ i : Fin 2, disk (![a, b] i) 1) = disk a 1 ∪ disk b 1 := by
  ext x
  simp only [mem_iUnion, mem_union, Fin.exists_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one]

lemma tp_iUnion_three (a b c : Pt) :
    (⋃ i : Fin 3, disk (![a, b, c] i) 1) = disk a 1 ∪ disk b 1 ∪ disk c 1 := by
  ext x
  simp only [mem_iUnion, mem_union, Fin.exists_fin_succ, Fin.exists_fin_zero, Matrix.cons_val_zero,
    Matrix.cons_val_succ, or_false, or_assoc]

/-- `A_1(z) = A({0, z}) - π` -/
lemma tp_A1_eq_union (z : Pt) : A1 z = unionArea ![(0 : Pt), z] - π := by
  unfold A1 unionArea
  rw [tp_iUnion_two, tp_vol_diff_eq (measurableSet_disk _ _) (measurableSet_disk _ _) (tp_volume_disk_ne_top _)
    (tp_volume_disk_ne_top _), volume_disk_one, ENNReal.toReal_ofReal Real.pi_pos.le]

/-- the half-turn is `rotL π` -/
lemma tp_rotL_pi (z : Pt) : rotL π z = -z := by
  rw [rotL_apply, Real.cos_pi, Real.sin_pi]
  ext <;> simp

lemma tp_A1_neg (w : Pt) : A1 (-w) = A1 w := by
  unfold A1
  have hpre : rotL π ⁻¹' (disk (-w) 1 \ disk 0 1) = disk w 1 \ disk 0 1 := by
    ext x
    simp only [mem_preimage, mem_sdiff, disk, mem_ofPred_eq, tp_rotL_pi]
    have e1 : sqDist (-x) (-w) = sqDist x w := by
      unfold sqDist; simp only [Prod.fst_neg, Prod.snd_neg]; ring
    have e2 : sqDist (-x) 0 = sqDist x 0 := by
      unfold sqDist; simp only [Prod.fst_neg, Prod.snd_neg, Prod.fst_zero, Prod.snd_zero]; ring
    rw [e1, e2]
  have hm : MeasurableSet (disk (-w) 1 \ disk 0 1) := (measurableSet_disk _ _).diff (measurableSet_disk _ _)
  rw [← hpre, (mp_rotL π).measure_preimage hm.nullMeasurableSet]

/-- T5: `A_1(z) = A1c(|z|)` -/
theorem a1Radial : A1Radial := by
  intro hG z
  rw [tp_A1_eq_union]
  set r := enorm2 z with hr
  have hr0 : 0 ≤ r := tp_enorm2_nonneg z
  -- rotate `(r, 0)` onto `z`
  obtain ⟨φ, hφ⟩ : ∃ φ, rotL φ (r, 0) = z := by
    refine ⟨Complex.arg ⟨z.1, z.2⟩, ?_⟩
    have hn : r = ‖(⟨z.1, z.2⟩ : ℂ)‖ := by rw [hr, tp_enorm2_eq_norm]
    rw [rotL_apply]
    have h1 := Complex.norm_mul_cos_arg (⟨z.1, z.2⟩ : ℂ)
    have h2 := Complex.norm_mul_sin_arg (⟨z.1, z.2⟩ : ℂ)
    rw [← hn] at h1 h2
    ext
    · simp only [mul_zero, sub_zero]; linarith [h1]
    · simp only [mul_zero, add_zero]; linarith [h2]
  have hu : unionArea ![(0 : Pt), z] = unionArea (TD.two r) := by
    have := unionArea_rotL φ (TD.two r)
    rw [← this]
    congr 1
    funext i
    fin_cases i
    · show (0 : Pt) = rotL φ ((0 : ℝ), (0 : ℝ))
      rw [rotL_apply]; ext <;> simp
    · show z = rotL φ (r, 0)
      exact hφ.symm
  rw [hu]
  rcases eq_or_lt_of_le hr0 with h0 | h0
  · -- `z = 0`
    have hz : z = 0 := by
      have h := tp_enorm2_sq z
      rw [← hr, ← h0] at h
      have h1 : z.1 = 0 := by nlinarith [sq_nonneg z.1, sq_nonneg z.2]
      have h2 : z.2 = 0 := by nlinarith [sq_nonneg z.1, sq_nonneg z.2]
      exact Prod.ext h1 h2
    rw [← h0]
    have h00 : unionArea (TD.two 0) = π := by
      unfold unionArea TD.two
      rw [tp_iUnion_two, show ((0 : ℝ), (0 : ℝ)) = (0 : Pt) from rfl, union_self, volume_disk_one,
        ENNReal.toReal_ofReal Real.pi_pos.le]
    have h02 : (0 : ℝ) < 2 := by norm_num
    rw [h00, A1c]
    simp only [h02, ↓reduceIte, a1f_zero]
    ring
  · rcases lt_or_ge r 2 with h2 | h2
    · rw [TD.unionArea_two hG h0 h2, A1c]
      simp only [h2, ↓reduceIte, a1f]
      ring
    · have h2' : ¬ r < 2 := not_lt.2 h2
      rw [TD.unionArea_two_far hG h2, A1c]
      simp only [h2', ↓reduceIte]
      ring

/-- T5: `A_2(w, z) = A(-w, 0, z) - π - A_1(w)` -/
theorem a2Union : A2Union := by
  intro w z
  unfold A2 unionArea
  have hm := measurableSet_disk
  have hf := tp_volume_disk_ne_top
  rw [tp_iUnion_three]
  -- `|B(z) \ (B(0) ∪ B(-w))| = |B(0) ∪ B(-w) ∪ B(z)| - |B(0) ∪ B(-w)|`
  have hA : MeasurableSet (disk 0 1 ∪ disk (-w) 1) := (hm _ _).union (hm _ _)
  have hAf : volume (disk 0 1 ∪ disk (-w) 1) ≠ ⊤ := measure_union_ne_top (hf _) (hf _)
  rw [tp_vol_diff_eq hA (hm _ _) hAf (hf _)]
  have e1 : disk 0 1 ∪ disk (-w) 1 ∪ disk z 1 = disk (-w) 1 ∪ disk 0 1 ∪ disk z 1 := by
    rw [union_comm (disk 0 1) (disk (-w) 1)]
  have e2 : (volume (disk 0 1 ∪ disk (-w) 1)).toReal = π + A1 w := by
    rw [← tp_A1_neg, tp_A1_eq_union]
    unfold unionArea
    rw [tp_iUnion_two]
    ring
  rw [e1, e2]
  ring

/-- T5: `A_2(w, z) ≤ A_1(z)` -/
theorem a2LeA1 : A2LeA1 := by
  intro w z
  unfold A2 A1
  exact ENNReal.toReal_mono (measure_ne_top_of_subset sdiff_subset (tp_volume_disk_ne_top z))
    (measure_mono (sdiff_subset_sdiff_right subset_union_left))

end BHH.W2
