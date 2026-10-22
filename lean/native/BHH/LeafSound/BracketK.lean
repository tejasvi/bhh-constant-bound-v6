/-
Module D, part 12: module C's bracket (`BracketProp`, stated on `Fin (m + 1)`) on the coordinates `Fin (mDim k)` of the
box part, `k = 3, 4, 5` (coordinate 0 is `r_2`).
-/
import BHH.LeafSound.Grad

open BHH.Cert Real MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace BHH

/-- `BracketProp` on `Fin (mDim k)` with the distinguished coordinate `0` read by `xget` -/
def BracketPropK (k : ℕ) : Prop :=
  ∀ (lo hi : Fin (mDim k) → ℝ) (s a Rbar Sbar : ℝ) (b : Fin (mDim k) → ℝ)
    (ρ : (Fin (mDim k) → ℝ) → ℝ) (f : (Fin (mDim k) → ℝ) → ℝ≥0∞),
    (∀ d, lo d < hi d) → 0 ≤ xget lo 0 → 0 < s → 0 ≤ Rbar → 0 ≤ Sbar →
    Measurable ρ → (∃ M, ∀ x ∈ rbox lo hi, 0 ≤ ρ x ∧ ρ x ≤ M) →
    (∫ x in rbox lo hi, ρ x) ≤ Rbar * (volume (rbox lo hi)).toReal →
    (∫ x in rbox lo hi, ρ x ^ 2) ≤ Sbar ^ 2 * (volume (rbox lo hi)).toReal →
    let v := ∏ d, (hi d - lo d)
    let c : Fin (mDim k) → ℝ := fun d => (lo d + hi d) / 2
    let h0 := xget hi 0 - xget lo 0
    let τ := a - ∑ d, |b d| * (hi d - lo d) / 2
    let Sb := √(∑ d, (b d) ^ 2 * (hi d - lo d) ^ 2 / 12)
    0 < τ →
    (∀ x ∈ rbox lo hi, ENNReal.ofReal (xget x 0 * phiS s (a + ∑ d, b d * (x d - c d) + ρ x)) ≤ f x) →
    let rbar := xget c 0
    let d1 := fun t : ℝ => -s * t ^ (-s - 1)
    let d2 := fun t : ℝ => s * (s + 1) * t ^ (-s - 2)
    let VB := rbar * phiS s (a + Rbar) + d1 a * (xget b 0 * h0 ^ 2 / 12) - |d1 a| * (h0 / 2) * Rbar
      - h0 / 4 * d2 τ * (Sb + Sbar) ^ 2
    let VA := rbar * phiS s (a + Rbar) + d1 (a + Rbar) * (xget b 0 * h0 ^ 2 / 12) - |d1 (a + Rbar)| * (h0 / 2) * Rbar
      - h0 / 4 * d2 τ * (Sb + √(Sbar ^ 2 + Rbar ^ 2)) ^ 2
    ENNReal.ofReal (v * max VB VA) ≤ ∫⁻ x in rbox lo hi, f x

theorem bracketPropK_of (hB : BracketProp) {k : ℕ} (hk3 : 3 ≤ k) (hk5 : k ≤ 5) : BracketPropK k := by
  interval_cases k
  · exact hB 2
  · exact hB 4
  · exact hB 6

end BHH
