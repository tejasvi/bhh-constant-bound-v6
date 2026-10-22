/-
The constants `κ_k = 2π Γ(k - 1/2) (k-2)! / k!` for `k = 3, 4, 5` (module E, item 4).

`κ_3 = π^{3/2}/4`, `κ_4 = 5 π^{3/2}/16`, `κ_5 = 21 π^{3/2}/32`, from `Γ(1/2) = √π` and `Γ(s + 1) = s Γ(s)`, and
rational lower bounds from `π > 3.14159265358979323846` (`Real.pi_gt_d20`).
-/
import BHH.Interfaces

open Real

namespace BHH.E

/-- `π^{3/2} = π √π` is at least this rational. -/
def piThreeHalvesLo : ℝ := 3.14159265358979323846 * 1.7724538509055160272

lemma sqrt_pi_gt : (1.7724538509055160272 : ℝ) < √π := by
  rw [Real.lt_sqrt (by norm_num)]
  calc (1.7724538509055160272 : ℝ) ^ 2 < 3.14159265358979323846 := by norm_num
    _ < π := Real.pi_gt_d20

lemma piThreeHalvesLo_lt : piThreeHalvesLo < π * √π := by
  unfold piThreeHalvesLo
  exact mul_lt_mul Real.pi_gt_d20 sqrt_pi_gt.le (by norm_num) Real.pi_pos.le

lemma Gamma_three_halves : Real.Gamma (3 / 2) = 1 / 2 * √π := by
  have h := Real.Gamma_add_one (s := 1 / 2) (by norm_num)
  rw [show (1 / 2 : ℝ) + 1 = 3 / 2 by norm_num, Real.Gamma_one_half_eq] at h
  exact h

lemma Gamma_five_halves : Real.Gamma (5 / 2) = 3 / 4 * √π := by
  have h := Real.Gamma_add_one (s := 3 / 2) (by norm_num)
  rw [show (3 / 2 : ℝ) + 1 = 5 / 2 by norm_num, Gamma_three_halves] at h
  rw [h]; ring

lemma Gamma_seven_halves : Real.Gamma (7 / 2) = 15 / 8 * √π := by
  have h := Real.Gamma_add_one (s := 5 / 2) (by norm_num)
  rw [show (5 / 2 : ℝ) + 1 = 7 / 2 by norm_num, Gamma_five_halves] at h
  rw [h]; ring

lemma Gamma_nine_halves : Real.Gamma (9 / 2) = 105 / 16 * √π := by
  have h := Real.Gamma_add_one (s := 7 / 2) (by norm_num)
  rw [show (7 / 2 : ℝ) + 1 = 9 / 2 by norm_num, Gamma_seven_halves] at h
  rw [h]; ring

theorem kappa_three : kappa 3 = 1 / 4 * (π * √π) := by
  unfold kappa
  rw [show ((3 : ℕ) : ℝ) - 1 / 2 = 5 / 2 by norm_num, Gamma_five_halves]
  simp [Nat.factorial]
  ring

theorem kappa_four : kappa 4 = 5 / 16 * (π * √π) := by
  unfold kappa
  rw [show ((4 : ℕ) : ℝ) - 1 / 2 = 7 / 2 by norm_num, Gamma_seven_halves]
  simp [Nat.factorial]
  ring

theorem kappa_five : kappa 5 = 21 / 32 * (π * √π) := by
  unfold kappa
  rw [show ((5 : ℕ) : ℝ) - 1 / 2 = 9 / 2 by norm_num, Gamma_nine_halves]
  simp [Nat.factorial]
  ring

theorem kappa_three_gt : 1 / 4 * piThreeHalvesLo < kappa 3 := by
  rw [kappa_three]; linarith [piThreeHalvesLo_lt]

theorem kappa_four_gt : 5 / 16 * piThreeHalvesLo < kappa 4 := by
  rw [kappa_four]; linarith [piThreeHalvesLo_lt]

theorem kappa_five_gt : 21 / 32 * piThreeHalvesLo < kappa 5 := by
  rw [kappa_five]; linarith [piThreeHalvesLo_lt]

end BHH.E

namespace BHH

-- the deliverables of this file, also under `BHH` (helpers stay in `BHH.E`)
export E (piThreeHalvesLo piThreeHalvesLo_lt kappa_three kappa_four kappa_five kappa_three_gt kappa_four_gt kappa_five_gt)

end BHH
