/-
The closed form of `A_1(r) = |B(z,1) \ B(0,1)|`, `|z| = r` (paper Section 4.3):
`A_1(r) = π - 2 arccos(r/2) + (r/2) √(4 - r²)` for `r ≤ 2`, `π` for `r ≥ 2`; it is nondecreasing on `[0, ∞)`
(derivative `√(4 - r²)`).  (That the closed form is the area is a separate statement.)
-/
import Mathlib

open Real Set

namespace BHH.W2

/-- `π - 2 arccos(r/2) + (r/2) √(4 - r²)` -/
noncomputable def a1f (r : ℝ) : ℝ := π - 2 * Real.arccos (r / 2) + (r / 2) * √(4 - r ^ 2)

/-- The closed form of `A_1`: `a1f` below `2`, `π` from `2` on. -/
noncomputable def A1c (r : ℝ) : ℝ := if r < 2 then a1f r else π

lemma a1f_two : a1f 2 = π := by
  unfold a1f; norm_num

lemma a1f_zero : a1f 0 = 0 := by
  unfold a1f; simp [Real.arccos_zero]; ring

lemma hasDerivAt_a1f {r : ℝ} (h0 : 0 < r) (h2 : r < 2) : HasDerivAt a1f (√(4 - r ^ 2)) r := by
  have hs : 0 < 4 - r ^ 2 := by nlinarith
  have hr1 : r / 2 ≠ -1 := by intro h; linarith
  have hr2 : r / 2 ≠ 1 := by intro h; linarith
  have hid : HasDerivAt (fun x : ℝ => x / 2) (1 / 2) r := by
    simpa using (hasDerivAt_id r).div_const 2
  have d1' := HasDerivAt.comp (h₂ := Real.arccos) r (Real.hasDerivAt_arccos hr1 hr2) hid
  have d1 : HasDerivAt (fun x => Real.arccos (x / 2)) (-(1 / √(1 - (r / 2) ^ 2)) * (1 / 2)) r := d1'
  have hf : HasDerivAt (fun x : ℝ => 4 - x ^ 2) (-(2 * r)) r := by
    have := ((hasDerivAt_id r).pow 2).const_sub 4
    simpa using this
  have d2 : HasDerivAt (fun x => √(4 - x ^ 2)) ((-(2 * r)) / (2 * √(4 - r ^ 2))) r :=
    hf.sqrt (ne_of_gt hs)
  have d3 : HasDerivAt (fun x => (x / 2) * √(4 - x ^ 2))
      ((1 / 2) * √(4 - r ^ 2) + (r / 2) * ((-(2 * r)) / (2 * √(4 - r ^ 2)))) r := hid.mul d2
  have dtot : HasDerivAt (fun x => π - 2 * Real.arccos (x / 2) + (x / 2) * √(4 - x ^ 2))
      (0 - 2 * (-(1 / √(1 - (r / 2) ^ 2)) * (1 / 2)) +
        ((1 / 2) * √(4 - r ^ 2) + (r / 2) * ((-(2 * r)) / (2 * √(4 - r ^ 2))))) r :=
    ((hasDerivAt_const r π).sub (d1.const_mul 2)).add d3
  have hS : 0 < √(4 - r ^ 2) := Real.sqrt_pos.mpr hs
  have hsq : √(4 - r ^ 2) ^ 2 = 4 - r ^ 2 := Real.sq_sqrt hs.le
  have h1 : √(1 - (r / 2) ^ 2) = √(4 - r ^ 2) / 2 := by
    rw [show 1 - (r / 2) ^ 2 = (4 - r ^ 2) / 4 by ring, Real.sqrt_div' _ (by norm_num : (0:ℝ) ≤ 4)]
    rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)]
  have heq : (0 - 2 * (-(1 / √(1 - (r / 2) ^ 2)) * (1 / 2)) +
        ((1 / 2) * √(4 - r ^ 2) + (r / 2) * ((-(2 * r)) / (2 * √(4 - r ^ 2))))) = √(4 - r ^ 2) := by
    rw [h1]
    field_simp
    nlinarith [hsq]
  rw [heq] at dtot
  exact dtot

lemma a1f_continuousOn : ContinuousOn a1f (Icc 0 2) := by
  unfold a1f
  apply Continuous.continuousOn
  fun_prop

/-- `a1f` is nondecreasing on `[0, 2]`. -/
lemma a1f_mono : MonotoneOn a1f (Icc 0 2) := by
  apply monotoneOn_of_deriv_nonneg (convex_Icc 0 2) a1f_continuousOn
  · rw [interior_Icc]
    intro x hx
    exact (hasDerivAt_a1f hx.1 hx.2).differentiableAt.differentiableWithinAt
  · rw [interior_Icc]
    intro x hx
    rw [(hasDerivAt_a1f hx.1 hx.2).deriv]
    exact Real.sqrt_nonneg _

lemma a1f_le_pi {r : ℝ} (h0 : 0 ≤ r) (h2 : r ≤ 2) : a1f r ≤ π := by
  rw [← a1f_two]; exact a1f_mono ⟨h0, h2⟩ ⟨by norm_num, le_rfl⟩ h2

/-- `A1c` is nondecreasing on `[0, ∞)`. -/
lemma A1c_mono : MonotoneOn A1c (Ici 0) := by
  intro x hx y hy hxy
  unfold A1c
  have hx0 : 0 ≤ x := hx
  split_ifs with h1 h2 h2
  · exact a1f_mono ⟨hx0, h1.le⟩ ⟨le_trans hx0 hxy, h2.le⟩ hxy
  · exact a1f_le_pi hx0 h1.le
  · exact absurd (lt_of_le_of_lt hxy h2) h1
  · exact le_rfl

lemma A1c_nonneg {r : ℝ} (h0 : 0 ≤ r) : 0 ≤ A1c r := by
  have := A1c_mono (show (0:ℝ) ∈ Ici 0 from mem_Ici.mpr le_rfl) h0 h0
  unfold A1c at this ⊢
  simp only [show (0:ℝ) < 2 by norm_num, ite_true, a1f_zero] at this
  exact this

lemma A1c_le_pi (r : ℝ) (h0 : 0 ≤ r) : A1c r ≤ π := by
  unfold A1c; split_ifs with h
  · exact a1f_le_pi h0 h.le
  · exact le_rfl

end BHH.W2
