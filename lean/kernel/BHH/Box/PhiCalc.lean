/-
Module C: calculus for `φ(t) = t^{-s}` (`phiS`): derivatives, monotonicity, and the two-sided Taylor bound
`0 ≤ φ(z) - φ(p) - φ'(p)(z - p) ≤ φ''(τ)/2 (z - p)²` for `z, p ≥ τ > 0`.
-/
import BHH.Interfaces

open Set Real

noncomputable section

namespace BHH

/-- A function with nonpositive second derivative on `[τ, ∞)` lies below its tangents there. -/
lemma le_tangent_of_deriv2_nonpos {F F' F'' : ℝ → ℝ} {τ : ℝ}
    (hF : ∀ t, τ ≤ t → HasDerivAt F (F' t) t) (hF' : ∀ t, τ ≤ t → HasDerivAt F' (F'' t) t)
    (hF'' : ∀ t, τ ≤ t → F'' t ≤ 0) {z p : ℝ} (hz : τ ≤ z) (hp : τ ≤ p) :
    F z ≤ F p + F' p * (z - p) := by
  -- `F'` is antitone on `[τ, ∞)`
  have anti : ∀ u w, τ ≤ u → u ≤ w → F' w ≤ F' u := by
    intro u w hu huw
    rcases eq_or_lt_of_le huw with h | h
    · rw [h]
    obtain ⟨ξ, hξ, hξeq⟩ := exists_hasDerivAt_eq_slope F' F'' h
      (fun t ht => (hF' t (hu.trans ht.1)).continuousAt.continuousWithinAt)
      (fun t ht => hF' t (hu.trans ht.1.le))
    have h1 : F'' ξ ≤ 0 := hF'' ξ (hu.trans hξ.1.le)
    rw [hξeq, div_le_iff₀ (sub_pos.2 h)] at h1
    linarith
  rcases lt_trichotomy z p with h | h | h
  · obtain ⟨ξ, hξ, hξeq⟩ := exists_hasDerivAt_eq_slope F F' h
      (fun t ht => (hF t (hz.trans ht.1)).continuousAt.continuousWithinAt)
      (fun t ht => hF t (hz.trans ht.1.le))
    have h1 : F' p ≤ F' ξ := anti ξ p (hz.trans hξ.1.le) hξ.2.le
    rw [hξeq, le_div_iff₀ (sub_pos.2 h)] at h1
    nlinarith
  · rw [h]; simp
  · obtain ⟨ξ, hξ, hξeq⟩ := exists_hasDerivAt_eq_slope F F' h
      (fun t ht => (hF t (hp.trans ht.1)).continuousAt.continuousWithinAt)
      (fun t ht => hF t (hp.trans ht.1.le))
    have h1 : F' ξ ≤ F' p := anti p ξ hp hξ.1.le
    rw [hξeq, div_le_iff₀ (sub_pos.2 h)] at h1
    nlinarith

/-- `φ'(t) = -s t^{-s-1}` -/
def dphi (s t : ℝ) : ℝ := -s * t ^ (-s - 1)

/-- `φ''(t) = s (s+1) t^{-s-2}` -/
def d2phi (s t : ℝ) : ℝ := s * (s + 1) * t ^ (-s - 2)

lemma phiS_hasDerivAt (s : ℝ) {t : ℝ} (ht : 0 < t) : HasDerivAt (phiS s) (dphi s t) t := by
  have := Real.hasDerivAt_rpow_const (p := -s) (Or.inl ht.ne')
  unfold phiS dphi
  convert this using 1

lemma dphi_hasDerivAt (s : ℝ) {t : ℝ} (ht : 0 < t) : HasDerivAt (dphi s) (d2phi s t) t := by
  have := (Real.hasDerivAt_rpow_const (p := -s - 1) (Or.inl ht.ne')).const_mul (-s)
  unfold dphi d2phi
  convert this using 1
  rw [show -s - 1 - 1 = -s - 2 by ring]
  ring

lemma phiS_pos (s : ℝ) {t : ℝ} (ht : 0 < t) : 0 < phiS s t := Real.rpow_pos_of_pos ht _

lemma phiS_anti {s : ℝ} (hs : 0 ≤ s) {t u : ℝ} (ht : 0 < t) (htu : t ≤ u) : phiS s u ≤ phiS s t :=
  Real.rpow_le_rpow_of_nonpos ht htu (by linarith)

lemma d2phi_pos {s : ℝ} (hs : 0 < s) {t : ℝ} (ht : 0 < t) : 0 < d2phi s t := by
  unfold d2phi; have := Real.rpow_pos_of_pos ht (-s - 2); positivity

lemma d2phi_anti {s : ℝ} (hs : 0 < s) {t u : ℝ} (ht : 0 < t) (htu : t ≤ u) : d2phi s u ≤ d2phi s t := by
  unfold d2phi
  have h := Real.rpow_le_rpow_of_nonpos ht htu (show -s - 2 ≤ 0 by linarith)
  have : 0 < s * (s + 1) := by positivity
  exact mul_le_mul_of_nonneg_left h this.le

lemma dphi_neg {s : ℝ} (hs : 0 < s) {t : ℝ} (ht : 0 < t) : dphi s t < 0 := by
  unfold dphi; have := Real.rpow_pos_of_pos ht (-s - 1); nlinarith

/-- Taylor bounds for `φ = phiS s` on `[τ, ∞)`, `τ > 0`. -/
lemma phiS_taylor {s τ z p : ℝ} (hs : 0 < s) (hτ : 0 < τ) (hz : τ ≤ z) (hp : τ ≤ p) :
    0 ≤ phiS s z - phiS s p - dphi s p * (z - p) ∧
    phiS s z - phiS s p - dphi s p * (z - p) ≤ d2phi s τ / 2 * (z - p) ^ 2 := by
  constructor
  · -- `-φ` has nonpositive second derivative
    have := le_tangent_of_deriv2_nonpos (F := fun t => -phiS s t) (F' := fun t => -dphi s t)
      (F'' := fun t => -d2phi s t) (τ := τ)
      (fun t ht => (phiS_hasDerivAt s (hτ.trans_le ht)).neg)
      (fun t ht => (dphi_hasDerivAt s (hτ.trans_le ht)).neg)
      (fun t ht => by have := d2phi_pos hs (hτ.trans_le ht); linarith) hz hp
    linarith
  · set K := d2phi s τ
    have := le_tangent_of_deriv2_nonpos (F := fun t => phiS s t - K / 2 * (t - p) ^ 2)
      (F' := fun t => dphi s t - K * (t - p)) (F'' := fun t => d2phi s t - K) (τ := τ)
      (fun t ht => by
        have h1 := phiS_hasDerivAt s (hτ.trans_le ht)
        have h2 : HasDerivAt (fun x => K / 2 * (x - p) ^ 2) (K * (t - p)) t := by
          have h := (((hasDerivAt_id' t).sub_const p).pow 2).const_mul (K / 2)
          convert h using 1
          push_cast; ring
        exact h1.sub h2)
      (fun t ht => by
        have h1 := dphi_hasDerivAt s (hτ.trans_le ht)
        have h2 : HasDerivAt (fun x => K * (x - p)) K t := by
          have h := ((hasDerivAt_id' t).sub_const p).const_mul K
          convert h using 1
          ring
        exact h1.sub h2)
      (fun t ht => by have := d2phi_anti hs hτ ht; linarith) hz hp
    simp only [sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, sub_zero] at this
    linarith

end BHH
