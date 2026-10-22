/-
Module T: positive exponential sums `f(t) = Σ c_i e^{-a_i t}` (`c_i, a_i ≥ 0`) are positive
everywhere once positive somewhere, nonincreasing, and log-convex (weighted AM-GM); secant minorants of convex
functions; the pointwise comparison of integrands behind each minorant.
-/
import W2.Interfaces

open MeasureTheory Set Real
open scoped ENNReal

noncomputable section

namespace BHH.W2

variable {f : ℝ → ℝ}

lemma expSum_pos (hf : IsExpSum f) {t₀ : ℝ} (h0 : 0 < f t₀) (t : ℝ) : 0 < f t := by
  obtain ⟨n, c, a, hc, ha, hfe⟩ := hf
  rw [hfe] at h0 ⊢
  by_contra hneg
  have hneg' := not_lt.1 hneg
  have hnn : ∀ j ∈ Finset.univ, 0 ≤ c j * Real.exp (-(a j * t)) := fun j _ => mul_nonneg (hc j) (exp_pos _).le
  have hsum0 : ∑ j, c j * Real.exp (-(a j * t)) = 0 := le_antisymm hneg' (Finset.sum_nonneg hnn)
  have hall : ∀ i, c i = 0 := by
    intro i
    have := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 hsum0 i (Finset.mem_univ i)
    rcases mul_eq_zero.1 this with h | h
    · exact h
    · exact absurd h (exp_pos _).ne'
  simp [hall] at h0

lemma expSum_anti (hf : IsExpSum f) : Antitone f := by
  obtain ⟨n, c, a, hc, ha, hfe⟩ := hf
  intro s t hst
  rw [hfe, hfe]
  exact Finset.sum_le_sum fun i _ =>
    mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (neg_le_neg (mul_le_mul_of_nonneg_left hst (ha i)))) (hc i)

lemma expSum_logConvex (hf : IsExpSum f) (hpos : ∀ t, 0 < f t) :
    ConvexOn ℝ univ (fun t => Real.log (f t)) := by
  obtain ⟨n, c, a, hc, ha, hfe⟩ := hf
  refine ⟨convex_univ, fun x _ y _ p q hp hq hpq => ?_⟩
  simp only [smul_eq_mul]
  have hA := hpos x
  have hB := hpos y
  have hApos := Real.rpow_pos_of_pos hA p
  have hBpos := Real.rpow_pos_of_pos hB q
  have hterm : ∀ i, c i * Real.exp (-(a i * (p * x + q * y))) ≤
      f x ^ p * f y ^ q * (p * (c i * Real.exp (-(a i * x)) / f x) + q * (c i * Real.exp (-(a i * y)) / f y)) := by
    intro i
    have hCx : 0 ≤ c i * Real.exp (-(a i * x)) := mul_nonneg (hc i) (exp_pos _).le
    have hCy : 0 ≤ c i * Real.exp (-(a i * y)) := mul_nonneg (hc i) (exp_pos _).le
    have hgm := Real.geom_mean_le_arith_mean2_weighted hp hq (div_nonneg hCx hA.le) (div_nonneg hCy hB.le) hpq
    rw [Real.div_rpow hCx hA.le, Real.div_rpow hCy hB.le] at hgm
    have hprod : (c i * Real.exp (-(a i * x))) ^ p * (c i * Real.exp (-(a i * y))) ^ q =
        c i * Real.exp (-(a i * (p * x + q * y))) := by
      rw [Real.mul_rpow (hc i) (exp_pos _).le, Real.mul_rpow (hc i) (exp_pos _).le, ← Real.exp_mul, ← Real.exp_mul]
      have hcpq : c i ^ p * c i ^ q = c i := by
        rw [← Real.rpow_add' (hc i) (by rw [hpq]; exact one_ne_zero), hpq, Real.rpow_one]
      calc c i ^ p * Real.exp (-(a i * x) * p) * (c i ^ q * Real.exp (-(a i * y) * q))
          = (c i ^ p * c i ^ q) * (Real.exp (-(a i * x) * p) * Real.exp (-(a i * y) * q)) := by ring
        _ = c i * Real.exp (-(a i * (p * x + q * y))) := by
          rw [hcpq, ← Real.exp_add]; congr 2; ring
    rw [← hprod]
    have e : (c i * Real.exp (-(a i * x))) ^ p * (c i * Real.exp (-(a i * y))) ^ q =
        ((c i * Real.exp (-(a i * x))) ^ p / f x ^ p * ((c i * Real.exp (-(a i * y))) ^ q / f y ^ q)) *
          (f x ^ p * f y ^ q) := by
      field_simp
    rw [e]
    calc _ ≤ (p * (c i * Real.exp (-(a i * x)) / f x) + q * (c i * Real.exp (-(a i * y)) / f y)) *
          (f x ^ p * f y ^ q) := mul_le_mul_of_nonneg_right hgm (by positivity)
      _ = _ := by ring
  have hsum : f (p * x + q * y) ≤ f x ^ p * f y ^ q := by
    rw [hfe (p * x + q * y)]
    calc ∑ i, c i * Real.exp (-(a i * (p * x + q * y)))
        ≤ ∑ i, f x ^ p * f y ^ q *
          (p * (c i * Real.exp (-(a i * x)) / f x) + q * (c i * Real.exp (-(a i * y)) / f y)) :=
          Finset.sum_le_sum fun i _ => hterm i
      _ = f x ^ p * f y ^ q * (p * ((∑ i, c i * Real.exp (-(a i * x))) / f x) +
          q * ((∑ i, c i * Real.exp (-(a i * y))) / f y)) := by
          rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_div,
            Finset.sum_div]
      _ = f x ^ p * f y ^ q := by
          rw [← hfe x, ← hfe y, div_self hA.ne', div_self hB.ne', mul_one, mul_one, hpq, mul_one]
  calc Real.log (f (p * x + q * y)) ≤ Real.log (f x ^ p * f y ^ q) := Real.log_le_log (hpos _) hsum
    _ = p * Real.log (f x) + q * Real.log (f y) := by
      rw [Real.log_mul hApos.ne' hBpos.ne', Real.log_rpow hA, Real.log_rpow hB]

/-- right of a secant: `ψ(t) ≥ ψ(y) + slope(x, y) (t - y)` for `x < y ≤ t` -/
lemma secant_right {ψ : ℝ → ℝ} (hψ : ConvexOn ℝ univ ψ) {x y t : ℝ} (hxy : x < y) (hyt : y ≤ t) :
    ψ y + (ψ y - ψ x) / (y - x) * (t - y) ≤ ψ t := by
  rcases eq_or_lt_of_le hyt with h | h
  · subst h; simp
  · have := hψ.slope_mono_adjacent (mem_univ x) (mem_univ t) hxy h
    rw [le_div_iff₀ (sub_pos.2 h)] at this
    linarith

/-- left of a secant: `ψ(t) ≥ ψ(x) + slope(x, y) (t - x)` for `t ≤ x < y` -/
lemma secant_left {ψ : ℝ → ℝ} (hψ : ConvexOn ℝ univ ψ) {x y t : ℝ} (hxy : x < y) (htx : t ≤ x) :
    ψ x + (ψ y - ψ x) / (y - x) * (t - x) ≤ ψ t := by
  rcases eq_or_lt_of_le htx with h | h
  · subst h; simp
  · have := hψ.slope_mono_adjacent (mem_univ t) (mem_univ y) h hxy
    rw [div_le_iff₀ (sub_pos.2 h)] at this
    linarith

/-- an affine minorant `A + σ t` of `log f` and `γ ≥ π - σ` give `t^c e^{A - γ t} ≤ t^c e^{-π t} f(t)` (`t ≥ 0`) -/
lemma minorant_integrand {t A σ γ c : ℝ} (ht : 0 ≤ t) (hft : 0 < f t) (hlog : A + σ * t ≤ Real.log (f t))
    (hγ : π - σ ≤ γ) : t ^ c * Real.exp (A - γ * t) ≤ t ^ c * Real.exp (-(π * t)) * f t := by
  have h1 : Real.exp (A - γ * t) ≤ Real.exp (-(π * t)) * f t := by
    rw [← Real.exp_log hft, ← Real.exp_add]
    apply Real.exp_le_exp.2
    nlinarith [mul_le_mul_of_nonneg_right hγ ht]
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg ht c)

end BHH.W2
