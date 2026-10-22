/-
Module G: Lemma 4 over the reals (`QuadBox`): the range of `f = r² + q² + 2 r q c` over a box
`[r1, r2] × [q1, q2] × [c1, c2]` (`r1, q1 ≥ 0`, `-1 ≤ c1`, `c2 ≤ 1`): at most the largest corner value at `c2`, at least
a corner value at `c1` or (if `c1 < 0`) an edge minimum `r1² (1 - c1²)` / `q1² (1 - c1²)`.
-/
import Mathlib

namespace BHH.W2

/-- a quadratic with leading coefficient `1` on `[x1, x2]` is at most its larger endpoint value -/
lemma quad_le_max {x1 x2 x β γ : ℝ} (h1 : x1 ≤ x) (h2 : x ≤ x2) :
    x ^ 2 + β * x + γ ≤ max (x1 ^ 2 + β * x1 + γ) (x2 ^ 2 + β * x2 + γ) := by
  rcases eq_or_lt_of_le (h1.trans h2) with h | h
  · have hx1 : x = x1 := le_antisymm (h ▸ h2) h1
    subst hx1
    exact le_max_left _ _
  · have hw : 0 < x2 - x1 := sub_pos.2 h
    -- f(x) ≤ ((x2 - x) f(x1) + (x - x1) f(x2)) / (x2 - x1)
    have key : (x ^ 2 + β * x + γ) * (x2 - x1) ≤
        (x2 - x) * (x1 ^ 2 + β * x1 + γ) + (x - x1) * (x2 ^ 2 + β * x2 + γ) := by
      nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)]
    set M := max (x1 ^ 2 + β * x1 + γ) (x2 ^ 2 + β * x2 + γ)
    have hM1 : x1 ^ 2 + β * x1 + γ ≤ M := le_max_left _ _
    have hM2 : x2 ^ 2 + β * x2 + γ ≤ M := le_max_right _ _
    have : (x ^ 2 + β * x + γ) * (x2 - x1) ≤ M * (x2 - x1) := by
      nlinarith [mul_le_mul_of_nonneg_left hM1 (sub_nonneg.2 h2), mul_le_mul_of_nonneg_left hM2 (sub_nonneg.2 h1)]
    exact le_of_mul_le_mul_right this hw

theorem quadBox_aux (r1 r2 q1 q2 c1 c2 r q c : ℝ) (hr1 : 0 ≤ r1) (hq1 : 0 ≤ q1) (hc1 : -1 ≤ c1) (hc2 : c2 ≤ 1)
    (hr : r1 ≤ r) (hr' : r ≤ r2) (hq : q1 ≤ q) (hq' : q ≤ q2) (hc : c1 ≤ c) (hc' : c ≤ c2) :
    let f := fun (x y z : ℝ) => x ^ 2 + y ^ 2 + 2 * x * y * z
    (f r q c ≤ max (max (f r1 q1 c2) (f r1 q2 c2)) (max (f r2 q1 c2) (f r2 q2 c2))) ∧
    (∃ v, (v = f r1 q1 c1 ∨ v = f r1 q2 c1 ∨ v = f r2 q1 c1 ∨ v = f r2 q2 c1 ∨
        (c1 < 0 ∧ ((v = r1 ^ 2 * (1 - c1 ^ 2) ∧ q1 ≤ -c1 * r1 ∧ -c1 * r1 ≤ q2) ∨
                   (v = q1 ^ 2 * (1 - c1 ^ 2) ∧ r1 ≤ -c1 * q1 ∧ -c1 * q1 ≤ r2)))) ∧ v ≤ f r q c) := by
  intro f
  have hr0 : 0 ≤ r := hr1.trans hr
  have hq0 : 0 ≤ q := hq1.trans hq
  have hrq : 0 ≤ r * q := mul_nonneg hr0 hq0
  -- monotone in `c`
  have hfc2 : f r q c ≤ f r q c2 := by
    show r ^ 2 + q ^ 2 + 2 * r * q * c ≤ r ^ 2 + q ^ 2 + 2 * r * q * c2
    nlinarith [mul_le_mul_of_nonneg_left hc' hrq]
  have hfc1 : f r q c1 ≤ f r q c := by
    show r ^ 2 + q ^ 2 + 2 * r * q * c1 ≤ r ^ 2 + q ^ 2 + 2 * r * q * c
    nlinarith [mul_le_mul_of_nonneg_left hc hrq]
  refine ⟨?_, ?_⟩
  · -- convex in `r` and in `q`: corners
    have h1 : f r q c2 ≤ max (f r1 q c2) (f r2 q c2) := by
      have := quad_le_max (β := 2 * q * c2) (γ := q ^ 2) hr hr'
      simp only [f]
      convert this using 1 <;> [ring; (congr 1 <;> ring)]
    have hq1' : ∀ x, f x q c2 ≤ max (f x q1 c2) (f x q2 c2) := by
      intro x
      have := quad_le_max (x := q) (β := 2 * x * c2) (γ := x ^ 2) hq hq'
      simp only [f]
      convert this using 1 <;> [ring; (congr 1 <;> ring)]
    refine hfc2.trans (h1.trans (max_le ?_ ?_))
    · exact (hq1' r1).trans (max_le ((le_max_left _ _).trans (le_max_left _ _))
        ((le_max_right _ _).trans (le_max_left _ _)))
    · exact (hq1' r2).trans (max_le ((le_max_left _ _).trans (le_max_right _ _))
        ((le_max_right _ _).trans (le_max_right _ _)))
  · -- the minimum at `c1`
    suffices hmin : ∃ v, (v = f r1 q1 c1 ∨ v = f r1 q2 c1 ∨ v = f r2 q1 c1 ∨ v = f r2 q2 c1 ∨
        (c1 < 0 ∧ ((v = r1 ^ 2 * (1 - c1 ^ 2) ∧ q1 ≤ -c1 * r1 ∧ -c1 * r1 ≤ q2) ∨
                   (v = q1 ^ 2 * (1 - c1 ^ 2) ∧ r1 ≤ -c1 * q1 ∧ -c1 * q1 ≤ r2)))) ∧ v ≤ f r q c1 by
      obtain ⟨v, hv, hle⟩ := hmin
      exact ⟨v, hv, hle.trans hfc1⟩
    simp only [f]
    rcases le_or_gt 0 c1 with hc0 | hc0
    · -- `c1 ≥ 0`: increasing in `r` and `q`
      refine ⟨_, Or.inl rfl, ?_⟩
      nlinarith [mul_le_mul hr hq hq1 hr0, mul_le_mul_of_nonneg_left (mul_le_mul hr hq hq1 hr0) hc0]
    · set κ := -c1 with hκ
      have hκ0 : 0 < κ := by linarith
      have hκ1 : κ ≤ 1 := by linarith
      have h1κ : 0 ≤ 1 - c1 ^ 2 := by nlinarith
      by_cases hA : q1 ≤ κ * r1 ∧ κ * r1 ≤ q2
      · refine ⟨_, Or.inr (Or.inr (Or.inr (Or.inr ⟨hc0, Or.inl ⟨rfl, hA.1, hA.2⟩⟩))), ?_⟩
        nlinarith [sq_nonneg (q + c1 * r), mul_le_mul_of_nonneg_left (mul_le_mul hr hr hr1 hr0) h1κ]
      by_cases hB : r1 ≤ κ * q1 ∧ κ * q1 ≤ r2
      · refine ⟨_, Or.inr (Or.inr (Or.inr (Or.inr ⟨hc0, Or.inr ⟨rfl, hB.1, hB.2⟩⟩))), ?_⟩
        nlinarith [sq_nonneg (r + c1 * q), mul_le_mul_of_nonneg_left (mul_le_mul hq hq hq1 hq0) h1κ]
      rcases lt_or_ge q2 (κ * r1) with hC | hC
      · -- `κ r1 > q2`: decreasing in `q`, then increasing in `r`: corner `(r1, q2)`
        refine ⟨_, Or.inr (Or.inl rfl), ?_⟩
        have hq2 : q ≤ κ * r := le_trans hq' (le_trans hC.le (mul_le_mul_of_nonneg_left hr hκ0.le))
        -- `g(r, q) ≥ g(r, q2)` and `g(r, q2) ≥ g(r1, q2)`
        have e1 : r ^ 2 + q ^ 2 + 2 * r * q * c1 - (r ^ 2 + q2 ^ 2 + 2 * r * q2 * c1) =
            (q2 - q) * (2 * κ * r - q - q2) := by rw [hκ]; ring
        have e2 : r ^ 2 + q2 ^ 2 + 2 * r * q2 * c1 - (r1 ^ 2 + q2 ^ 2 + 2 * r1 * q2 * c1) =
            (r - r1) * (r + r1 - 2 * κ * q2) := by rw [hκ]; ring
        have hq2' : κ * q2 ≤ r1 := by nlinarith [mul_le_mul_of_nonneg_left hC.le hκ0.le]
        have p1 : 0 ≤ (q2 - q) * (2 * κ * r - q - q2) := by
          apply mul_nonneg (by linarith)
          nlinarith [mul_le_mul_of_nonneg_left hr hκ0.le]
        have p2 : 0 ≤ (r - r1) * (r + r1 - 2 * κ * q2) := by
          apply mul_nonneg (by linarith)
          linarith
        linarith
      rcases lt_or_ge r2 (κ * q1) with hD | hD
      · -- `κ q1 > r2`: corner `(r2, q1)`
        refine ⟨_, Or.inr (Or.inr (Or.inl rfl)), ?_⟩
        have e1 : r ^ 2 + q ^ 2 + 2 * r * q * c1 - (r2 ^ 2 + q ^ 2 + 2 * r2 * q * c1) =
            (r2 - r) * (2 * κ * q - r - r2) := by rw [hκ]; ring
        have e2 : r2 ^ 2 + q ^ 2 + 2 * r2 * q * c1 - (r2 ^ 2 + q1 ^ 2 + 2 * r2 * q1 * c1) =
            (q - q1) * (q + q1 - 2 * κ * r2) := by rw [hκ]; ring
        have hr2' : κ * r2 ≤ q1 := by nlinarith [mul_le_mul_of_nonneg_left hD.le hκ0.le]
        have p1 : 0 ≤ (r2 - r) * (2 * κ * q - r - r2) := by
          apply mul_nonneg (by linarith)
          nlinarith [mul_le_mul_of_nonneg_left hq hκ0.le]
        have p2 : 0 ≤ (q - q1) * (q + q1 - 2 * κ * r2) := by
          apply mul_nonneg (by linarith)
          linarith
        linarith
      · -- `κ r1 < q1` and `κ q1 < r1`: corner `(r1, q1)` (gradient nonnegative there, PSD remainder)
        have hA' : κ * r1 < q1 := by
          by_contra h
          exact hA ⟨not_lt.1 h, hC⟩
        have hB' : κ * q1 < r1 := by
          by_contra h
          exact hB ⟨not_lt.1 h, hD⟩
        refine ⟨_, Or.inl rfl, ?_⟩
        have e : r ^ 2 + q ^ 2 + 2 * r * q * c1 - (r1 ^ 2 + q1 ^ 2 + 2 * r1 * q1 * c1) =
            2 * (r1 - κ * q1) * (r - r1) + 2 * (q1 - κ * r1) * (q - q1) +
              ((r - r1) ^ 2 + (q - q1) ^ 2 - 2 * κ * (r - r1) * (q - q1)) := by rw [hκ]; ring
        have psd : 0 ≤ (r - r1) ^ 2 + (q - q1) ^ 2 - 2 * κ * (r - r1) * (q - q1) := by
          nlinarith [sq_nonneg (r - r1 - (q - q1)), mul_nonneg (sub_nonneg.2 hr) (sub_nonneg.2 hq),
            mul_le_mul_of_nonneg_right hκ1 (mul_nonneg (sub_nonneg.2 hr) (sub_nonneg.2 hq))]
        have g1 : 0 ≤ 2 * (r1 - κ * q1) * (r - r1) := by
          apply mul_nonneg (by linarith) (by linarith)
        have g2 : 0 ≤ 2 * (q1 - κ * r1) * (q - q1) := by
          apply mul_nonneg (by linarith) (by linarith)
        linarith

end BHH.W2
