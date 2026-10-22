/-
Module T: the sub-interval bound used by `W2C.segLo` (paper Section 4.4).
For `0 < a < b`, `c ≥ 0`, `u(t) = c log t + α - γ t` and lower bounds `X ≤ u(a)`, `Y ≤ u(b)`:
`∫_a^b t^c e^{α - γ t} dt ≥ w e^{(X+Y)/2} (1 + (Y - X)²/24 + c w²/(12 b²))`, `w = b - a`
(chord + curvature of `log`, `e^x ≥ 1 + x`, and pairing `t` with `a + b - t`: `e^v + e^{-v} ≥ 2 + v²`).
-/
import Mathlib

open MeasureTheory Set Real

noncomputable section

namespace BHH.W2

lemma two_add_sq_le_exp_add_exp (v : ℝ) : 2 + v ^ 2 ≤ Real.exp v + Real.exp (-v) := by
  have e1 : Real.exp v = Real.exp (v / 2) ^ 2 := by rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  have e2 : Real.exp (-v) = Real.exp (-(v / 2)) ^ 2 := by rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  have e3 : Real.exp (v / 2) * Real.exp (-(v / 2)) = 1 := by rw [← Real.exp_add]; simp
  have h1 : Real.exp v + Real.exp (-v) - 2 = (Real.exp (v / 2) - Real.exp (-(v / 2))) ^ 2 := by
    rw [e1, e2]; linear_combination 2 * e3
  have h2 : Real.exp (v / 2) - Real.exp (-(v / 2)) = 2 * Real.sinh (v / 2) := by rw [Real.sinh_eq]; ring
  have h3 : (v / 2) ^ 2 ≤ Real.sinh (v / 2) ^ 2 := by
    rcases le_total 0 (v / 2) with hv | hv
    · have := Real.self_le_sinh_iff.2 hv
      nlinarith
    · have := Real.self_le_sinh_iff.2 (neg_nonneg.2 hv)
      rw [Real.sinh_neg] at this
      nlinarith
  rw [h2] at h1
  nlinarith [h3]

/-- strong concavity of `log` on `[a, b]`: `log t ≥ (chord through a, b) + (t - a)(b - t)/(2 b²)` -/
lemma log_chord_curv {a b t : ℝ} (ha : 0 < a) (hab : a < b) (ht : t ∈ Icc a b) :
    (b - t) / (b - a) * Real.log a + (t - a) / (b - a) * Real.log b + (t - a) * (b - t) / (2 * b ^ 2) ≤
      Real.log t := by
  have hb : 0 < b := ha.trans hab
  have hw : 0 < b - a := sub_pos.2 hab
  have hw0 : b - a ≠ 0 := hw.ne'
  have hb0 : b ≠ 0 := hb.ne'
  have hconv : ConvexOn ℝ (Icc a b) (fun x => -Real.log x - x ^ 2 / (2 * b ^ 2)) := by
    refine convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc a b) (f' := fun x => -x⁻¹ - x / b ^ 2)
      (f'' := fun x => (x ^ 2)⁻¹ - 1 / b ^ 2) ?_ ?_ ?_ ?_
    · refine ContinuousOn.sub (ContinuousOn.neg (Real.continuousOn_log.mono ?_)) (by fun_prop)
      intro x hx
      exact ne_of_gt (ha.trans_le hx.1)
    · intro x hx
      rw [interior_Icc] at hx
      have hx0 : x ≠ 0 := ne_of_gt (ha.trans hx.1)
      refine HasDerivAt.hasDerivWithinAt ?_
      have h1 := (Real.hasDerivAt_log hx0).neg
      have h2 := (hasDerivAt_pow 2 x).div_const (2 * b ^ 2)
      convert h1.sub h2 using 1
      push_cast
      field_simp
    · intro x hx
      rw [interior_Icc] at hx
      have hx0 : x ≠ 0 := ne_of_gt (ha.trans hx.1)
      refine HasDerivAt.hasDerivWithinAt ?_
      have h1 := (hasDerivAt_inv hx0).neg
      have h2 := (hasDerivAt_id' x).div_const (b ^ 2)
      convert h1.sub h2 using 1
      simp
    · intro x hx
      rw [interior_Icc] at hx
      have hx0 : 0 < x := ha.trans hx.1
      have hxb : x ^ 2 ≤ b ^ 2 := by nlinarith [hx.2]
      rw [sub_nonneg, one_div]
      exact inv_anti₀ (by positivity) hxb
  have hp : 0 ≤ (b - t) / (b - a) := div_nonneg (by linarith [ht.2]) hw.le
  have hq : 0 ≤ (t - a) / (b - a) := div_nonneg (by linarith [ht.1]) hw.le
  have hpq : (b - t) / (b - a) + (t - a) / (b - a) = 1 := by field_simp; ring
  have h := hconv.2 (left_mem_Icc.2 hab.le) (right_mem_Icc.2 hab.le) hp hq hpq
  have ht' : ((b - t) / (b - a)) • a + ((t - a) / (b - a)) • b = t := by
    simp only [smul_eq_mul]; field_simp; ring
  rw [ht'] at h
  simp only [smul_eq_mul] at h
  have e1 : (b - t) / (b - a) * (-Real.log a - a ^ 2 / (2 * b ^ 2)) +
      (t - a) / (b - a) * (-Real.log b - b ^ 2 / (2 * b ^ 2)) =
      -((b - t) / (b - a) * Real.log a + (t - a) / (b - a) * Real.log b) - (t - a) * (b - t) / (2 * b ^ 2) -
        t ^ 2 / (2 * b ^ 2) := by
    field_simp
    ring
  rw [e1] at h
  linarith

/-- the sub-interval bound -/
theorem sub_bound {a b c α γ X Y : ℝ} (ha : 0 < a) (hab : a < b) (hc : 0 ≤ c)
    (hX : X ≤ c * Real.log a + α - γ * a) (hY : Y ≤ c * Real.log b + α - γ * b) :
    (b - a) * Real.exp ((X + Y) / 2) * (1 + (Y - X) ^ 2 / 24 + c * (b - a) ^ 2 / (12 * b ^ 2)) ≤
      ∫ t in a..b, t ^ c * Real.exp (α - γ * t) := by
  have hw : 0 < b - a := sub_pos.2 hab
  have hw0 : b - a ≠ 0 := hw.ne'
  have hb : 0 < b := ha.trans hab
  have hb0 : b ≠ 0 := hb.ne'
  have hκ : 0 ≤ c / (2 * b ^ 2) := by positivity
  -- `G t = e^{ℓ(t)} (1 + κ (t - a)(b - t))`, `ℓ` the chord through `(a, X)`, `(b, Y)`
  set G : ℝ → ℝ := fun t => Real.exp ((X + Y) / 2 + (Y - X) * (t - (a + b) / 2) / (b - a)) *
    (1 + c / (2 * b ^ 2) * ((t - a) * (b - t))) with hGdef
  have hGc : Continuous G := by simp only [hGdef]; fun_prop
  have hpt : ∀ t ∈ Icc a b, G t ≤ t ^ c * Real.exp (α - γ * t) := by
    intro t ht
    have ht0 : 0 < t := ha.trans_le ht.1
    have hlog := log_chord_curv ha hab ht
    have hp : 0 ≤ (b - t) / (b - a) := div_nonneg (by linarith [ht.2]) hw.le
    have hq : 0 ≤ (t - a) / (b - a) := div_nonneg (by linarith [ht.1]) hw.le
    have hu : (X + Y) / 2 + (Y - X) * (t - (a + b) / 2) / (b - a) + c / (2 * b ^ 2) * ((t - a) * (b - t)) ≤
        c * Real.log t + α - γ * t := by
      have e1 : (X + Y) / 2 + (Y - X) * (t - (a + b) / 2) / (b - a) = (b - t) / (b - a) * X + (t - a) / (b - a) * Y := by
        field_simp; ring
      have e3 : (b - t) / (b - a) * (c * Real.log a + α - γ * a) + (t - a) / (b - a) * (c * Real.log b + α - γ * b) +
          c / (2 * b ^ 2) * ((t - a) * (b - t)) =
          c * ((b - t) / (b - a) * Real.log a + (t - a) / (b - a) * Real.log b + (t - a) * (b - t) / (2 * b ^ 2)) +
            α - γ * t := by
        field_simp; ring
      have h4 := mul_le_mul_of_nonneg_left hlog hc
      have h1 : (b - t) / (b - a) * X ≤ (b - t) / (b - a) * (c * Real.log a + α - γ * a) :=
        mul_le_mul_of_nonneg_left hX hp
      have h2 : (t - a) / (b - a) * Y ≤ (t - a) / (b - a) * (c * Real.log b + α - γ * b) :=
        mul_le_mul_of_nonneg_left hY hq
      rw [e1]
      linarith
    have hint : t ^ c * Real.exp (α - γ * t) = Real.exp (c * Real.log t + α - γ * t) := by
      rw [Real.rpow_def_of_pos ht0, ← Real.exp_add]; ring_nf
    rw [hint]
    calc G t = Real.exp ((X + Y) / 2 + (Y - X) * (t - (a + b) / 2) / (b - a)) *
          (1 + c / (2 * b ^ 2) * ((t - a) * (b - t))) := rfl
      _ ≤ Real.exp ((X + Y) / 2 + (Y - X) * (t - (a + b) / 2) / (b - a)) *
          Real.exp (c / (2 * b ^ 2) * ((t - a) * (b - t))) := by
          gcongr
          linarith [Real.add_one_le_exp (c / (2 * b ^ 2) * ((t - a) * (b - t)))]
      _ = Real.exp ((X + Y) / 2 + (Y - X) * (t - (a + b) / 2) / (b - a) +
          c / (2 * b ^ 2) * ((t - a) * (b - t))) := by rw [← Real.exp_add]
      _ ≤ Real.exp (c * Real.log t + α - γ * t) := Real.exp_le_exp.2 hu
  have hFi : IntervalIntegrable (fun t => t ^ c * Real.exp (α - γ * t)) volume a b := by
    have : Continuous (fun t : ℝ => t ^ c * Real.exp (α - γ * t)) :=
      (Real.continuous_rpow_const hc).mul (by fun_prop)
    exact this.intervalIntegrable a b
  have hGi : IntervalIntegrable G volume a b := hGc.intervalIntegrable a b
  have hGri : IntervalIntegrable (fun t => G (a + b - t)) volume a b :=
    (hGc.comp (by fun_prop : Continuous fun t : ℝ => a + b - t)).intervalIntegrable a b
  have hrefl : ∫ t in a..b, G (a + b - t) = ∫ t in a..b, G t := by
    rw [intervalIntegral.integral_comp_sub_left (fun t => G t) (a + b)]
    simp only [add_sub_cancel_right, add_sub_cancel_left]
  -- polynomial lower bound for `G t + G (a + b - t)`
  set P' : ℝ → ℝ := fun t => Real.exp ((X + Y) / 2) *
    (2 + ((Y - X) * (t - (a + b) / 2) / (b - a)) ^ 2 + 2 * (c / (2 * b ^ 2)) * ((t - a) * (b - t))) with hP'def
  have hpair : ∀ t ∈ Icc a b, P' t ≤ G t + G (a + b - t) := by
    intro t ht
    have hφ : 0 ≤ c / (2 * b ^ 2) * ((t - a) * (b - t)) :=
      mul_nonneg hκ (mul_nonneg (by linarith [ht.1]) (by linarith [ht.2]))
    set v := (Y - X) * (t - (a + b) / 2) / (b - a) with hvdef
    set F := c / (2 * b ^ 2) * ((t - a) * (b - t)) with hFdef
    have e1 : G (a + b - t) = Real.exp ((X + Y) / 2 - v) * (1 + F) := by
      simp only [hGdef, hvdef, hFdef]
      congr 2
      · ring
      · ring
    have e0 : G t = Real.exp ((X + Y) / 2 + v) * (1 + F) := rfl
    have e2 : Real.exp ((X + Y) / 2 + v) + Real.exp ((X + Y) / 2 - v) =
        Real.exp ((X + Y) / 2) * (Real.exp v + Real.exp (-v)) := by
      rw [mul_add, ← Real.exp_add, ← Real.exp_add]; ring_nf
    have hc2 := two_add_sq_le_exp_add_exp v
    have hE := Real.exp_pos ((X + Y) / 2)
    have hP' : P' t = Real.exp ((X + Y) / 2) * (2 + v ^ 2 + 2 * F) := by
      simp only [hP'def, hvdef, hFdef]; ring
    rw [e0, e1, hP']
    have e4 : Real.exp ((X + Y) / 2 + v) * (1 + F) + Real.exp ((X + Y) / 2 - v) * (1 + F) =
        Real.exp ((X + Y) / 2) * (Real.exp v + Real.exp (-v)) * (1 + F) := by
      rw [← e2]; ring
    rw [e4]
    have hv := sq_nonneg v
    nlinarith [mul_nonneg hE.le (sub_nonneg.2 hc2), mul_nonneg (mul_nonneg hE.le hφ) (sub_nonneg.2 hc2),
      mul_nonneg (mul_nonneg hE.le hφ) hv]
  have hP'i : IntervalIntegrable P' volume a b := by
    have : Continuous P' := by simp only [hP'def]; fun_prop
    exact this.intervalIntegrable a b
  -- antiderivative of `P'`
  set P : ℝ → ℝ := fun t => Real.exp ((X + Y) / 2) * (2 * t + (Y - X) ^ 2 / (3 * (b - a) ^ 2) * (t - (a + b) / 2) ^ 3 +
    2 * (c / (2 * b ^ 2)) * ((b - a) / 2 * (t - a) ^ 2 - 1 / 3 * (t - a) ^ 3)) with hPdef
  have hPd : ∀ x ∈ uIcc a b, HasDerivAt P (P' x) x := by
    intro x _
    have h1 : HasDerivAt (fun t => t - (a + b) / 2) 1 x := (hasDerivAt_id' x).sub_const _
    have h2 : HasDerivAt (fun t => t - a) 1 x := (hasDerivAt_id' x).sub_const a
    have h3 := (h1.fun_pow 3).const_mul ((Y - X) ^ 2 / (3 * (b - a) ^ 2))
    have h4 := (h2.fun_pow 2).const_mul ((b - a) / 2)
    have h5 := (h2.fun_pow 3).const_mul (1 / 3 : ℝ)
    have h6 := (((hasDerivAt_id' x).const_mul (2 : ℝ)).add h3).add ((h4.sub h5).const_mul (2 * (c / (2 * b ^ 2))))
    have h7 := h6.const_mul (Real.exp ((X + Y) / 2))
    convert h7 using 1
    simp only [hP'def]
    push_cast
    field_simp
    ring
  have hFTC : ∫ t in a..b, P' t = P b - P a := intervalIntegral.integral_eq_sub_of_hasDerivAt hPd hP'i
  have hPval : P b - P a = 2 * ((b - a) * Real.exp ((X + Y) / 2) *
      (1 + (Y - X) ^ 2 / 24 + c * (b - a) ^ 2 / (12 * b ^ 2))) := by
    simp only [hPdef]; field_simp; ring
  have hmono1 : ∫ t in a..b, P' t ≤ ∫ t in a..b, (G t + G (a + b - t)) :=
    intervalIntegral.integral_mono_on hab.le hP'i (hGi.add hGri) hpair
  have hadd : ∫ t in a..b, (G t + G (a + b - t)) = 2 * ∫ t in a..b, G t := by
    rw [intervalIntegral.integral_add hGi hGri, hrefl]; ring
  have hmono2 : ∫ t in a..b, G t ≤ ∫ t in a..b, t ^ c * Real.exp (α - γ * t) :=
    intervalIntegral.integral_mono_on hab.le hGi hFi hpt
  rw [hFTC, hPval, hadd] at hmono1
  linarith

end BHH.W2
