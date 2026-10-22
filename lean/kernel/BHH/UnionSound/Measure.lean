/-
Module B (union area), part 4: measure lemmas.

* `volume_modSet_le`: the points of `[0, 2π)` congruent mod `2π` to a point of `S` have measure `≤ volume S`
  (`[0, 2π]` is a fundamental domain of `2πℤ`).
* `abs_setIntegral_sub_le`: `|∫_E f - ∫_E' f| ≤ M S` if `|f| ≤ M` and `volume (E Δ E') ≤ S`.
-/
import BHH.UnionSound.Sweep

open BHH.Cert Real Set MeasureTheory
open scoped Pointwise

namespace BHH

noncomputable section

namespace US

/-- the points of `[0, 2π)` congruent mod `2π` to a point of `S` -/
def modSet (S : Set ℝ) : Set ℝ := {t | t ∈ Ico 0 (2 * π) ∧ ∃ n : ℤ, t + n * (2 * π) ∈ S}

lemma volume_modSet_le (S : Set ℝ) : volume (modSet S) ≤ volume S := by
  have hfd := isAddFundamentalDomain_Ioc Real.two_pi_pos 0 (μ := volume)
  rw [hfd.measure_eq_tsum S]
  calc volume (modSet S)
      ≤ volume ({0} ∪ ⋃ g : AddSubgroup.zmultiples (2 * π), ((g +ᵥ S) ∩ Ioc 0 (0 + 2 * π))) := by
        apply measure_mono
        rintro t ⟨ht, n, hn⟩
        by_cases h0 : t = 0
        · left; exact h0
        · right
          rw [mem_iUnion]
          refine ⟨⟨-(n * (2 * π)), AddSubgroup.mem_zmultiples_iff.mpr ⟨-n, by simp [zsmul_eq_mul]⟩⟩, ?_, ?_⟩
          · rw [mem_vadd_set_iff_neg_vadd_mem]
            have : -(⟨-(n * (2 * π)), AddSubgroup.mem_zmultiples_iff.mpr ⟨-n, by simp [zsmul_eq_mul]⟩⟩ :
                AddSubgroup.zmultiples (2 * π)) +ᵥ t = t + n * (2 * π) := by
              show -(-(n * (2 * π))) + t = t + n * (2 * π)
              ring
            rw [this]; exact hn
          · exact ⟨lt_of_le_of_ne ht.1 (Ne.symm h0), by linarith [ht.2]⟩
    _ ≤ volume ({0} : Set ℝ) + volume (⋃ g : AddSubgroup.zmultiples (2 * π), ((g +ᵥ S) ∩ Ioc 0 (0 + 2 * π))) :=
        measure_union_le _ _
    _ = volume (⋃ g : AddSubgroup.zmultiples (2 * π), ((g +ᵥ S) ∩ Ioc 0 (0 + 2 * π))) := by simp
    _ ≤ ∑' g : AddSubgroup.zmultiples (2 * π), volume ((g +ᵥ S) ∩ Ioc 0 (0 + 2 * π)) := measure_iUnion_le _

lemma volume_Ioo_diff_Icc_le {a b c d : ℝ} (hac : a ≤ c) (hdb : d ≤ b) :
    volume (Ioo a b \ Icc c d) ≤ ENNReal.ofReal ((c - a) + (b - d)) := by
  calc volume (Ioo a b \ Icc c d) ≤ volume (Ioo a c ∪ Ioo d b) := by
        apply measure_mono
        rintro t ⟨⟨h1, h2⟩, h3⟩
        rw [mem_Icc, not_and_or, not_le, not_le] at h3
        rcases h3 with h3 | h3
        · left; exact ⟨h1, h3⟩
        · right; exact ⟨h3, h2⟩
    _ ≤ volume (Ioo a c) + volume (Ioo d b) := measure_union_le _ _
    _ = ENNReal.ofReal (c - a) + ENNReal.ofReal (b - d) := by rw [Real.volume_Ioo, Real.volume_Ioo]
    _ = ENNReal.ofReal ((c - a) + (b - d)) := by
        rw [ENNReal.ofReal_add (by linarith) (by linarith)]

lemma measure_list_biUnion_le {α : Type*} (L : List α) (X : α → Set ℝ) :
    volume (⋃ p ∈ L, X p) ≤ (L.map fun p => volume (X p)).sum := by
  induction L with
  | nil => simp
  | cons a L ih =>
    simp only [List.mem_cons, iUnion_iUnion_eq_or_left, List.map_cons, List.sum_cons]
    exact le_trans (measure_union_le _ _) (add_le_add le_rfl ih)

lemma list_sum_ofReal {α : Type*} (L : List α) (f : α → ℝ) (hf : ∀ p ∈ L, 0 ≤ f p) :
    (L.map fun p => ENNReal.ofReal (f p)).sum = ENNReal.ofReal (L.map f).sum := by
  induction L with
  | nil => simp
  | cons a L ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [ih (fun p hp => hf p (List.mem_cons_of_mem _ hp)),
      ENNReal.ofReal_add (hf a (by simp)) (List.sum_nonneg (by
        intro x hx
        obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
        exact hf p (List.mem_cons_of_mem _ hp)))]

/-- `|∫_E f - ∫_E' f| ≤ M S` when `|f| ≤ M` and the symmetric difference has measure `≤ S`. -/
lemma abs_setIntegral_sub_le {f : ℝ → ℝ} {M S : ℝ} (hf : Continuous f) (hM : ∀ t, |f t| ≤ M) (hM0 : 0 ≤ M)
    (hS0 : 0 ≤ S) {E E' : Set ℝ} (hE : MeasurableSet E) (hE' : MeasurableSet E')
    (hEb : E ⊆ Icc 0 (2 * π)) (hE'b : E' ⊆ Icc 0 (2 * π))
    (hvol : volume ((E \ E') ∪ (E' \ E)) ≤ ENNReal.ofReal S) :
    |(∫ t in E, f t) - ∫ t in E', f t| ≤ M * S := by
  have hIcc : volume (Icc (0 : ℝ) (2 * π)) < ⊤ := measure_Icc_lt_top
  have hint : IntegrableOn f (Icc 0 (2 * π)) := hf.integrableOn_Icc
  have h1 := integral_inter_add_sdiff hE' (hint.mono_set hEb)
  have h2 := integral_inter_add_sdiff hE (hint.mono_set hE'b)
  rw [inter_comm] at h2
  have hfin1 : volume (E \ E') < ⊤ := lt_of_le_of_lt (measure_mono (sdiff_subset.trans hEb)) hIcc
  have hfin2 : volume (E' \ E) < ⊤ := lt_of_le_of_lt (measure_mono (sdiff_subset.trans hE'b)) hIcc
  have b1 := norm_setIntegral_le_of_norm_le_const (f := f) (C := M) hfin1
    (fun t _ => by rw [Real.norm_eq_abs]; exact hM t)
  have b2 := norm_setIntegral_le_of_norm_le_const (f := f) (C := M) hfin2
    (fun t _ => by rw [Real.norm_eq_abs]; exact hM t)
  rw [Real.norm_eq_abs, measureReal_def] at b1 b2
  have hsum : (volume (E \ E')).toReal + (volume (E' \ E)).toReal ≤ S := by
    rw [← ENNReal.toReal_add hfin1.ne hfin2.ne, ← measure_union disjoint_sdiff_sdiff (hE'.diff hE)]
    exact ENNReal.toReal_le_of_le_ofReal hS0 hvol
  have e : (∫ t in E, f t) - ∫ t in E', f t = (∫ t in E \ E', f t) - ∫ t in E' \ E, f t := by
    linarith [h1, h2]
  rw [e]
  have := abs_sub (∫ t in E \ E', f t) (∫ t in E' \ E, f t)
  nlinarith [b1, b2, hsum, hM0]

end US

end

end BHH
