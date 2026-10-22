/-
The statements of Theorem 1.1 of the paper, as `Prop`-valued definitions, with the window-3 constant as a parameter.

Hypotheses: `GreenFormula` (paper eq. (2.1)), `VertexLemmaSeg` (paper Lemma 3.1 with Remark 3.2 and eq. (2.2), along a
segment) and Dong-Cao's Theorem 3 with `K = 30` (`DongCaoK30`), exactly as in `BHH/StatementV2.lean`: there is
no new hypothesis.  Box part (k = 3, 4, 5; C5 from the refined run): `MainBoundsV3`.  Window-3 part
(6 <= k <= 22): `W3BoundAt w`, for the constant `w` that a computation certifies on its grid.
The paper's constants (grid (60,30,144)): `W3Bound` (`w = 0.0042404631`) and `BetaBoundV3` (`β ≥ 0.6508522354`).
-/
import BHH.DefsV2

open scoped ENNReal

namespace BHH

/-- Theorem 1.1 of the paper, the terms `k = 3, 4, 5`: `C_3 ≥ 0.0117130195`, `C_4 ≥ 0.0063707166`,
`C_5 ≥ 0.0035280362` (as `MainBoundsV2` with the refined `C_5`). -/
def MainBoundsV3 : Prop :=
  GreenFormula → VertexLemmaSeg →
    ENNReal.ofReal (117130195 / 10 ^ 10) ≤ C 3 ∧
    ENNReal.ofReal (63707166 / 10 ^ 10) ≤ C 4 ∧
    ENNReal.ofReal (35280362 / 10 ^ 10) ≤ C 5

/-- The terms `6 ≤ k ≤ 22` (window-3 bound) with the constant `w`: `Σ_{k=6}^{22} C_k ≥ w`. -/
def W3BoundAt (w : ℝ) : Prop :=
  GreenFormula → VertexLemmaSeg → ENNReal.ofReal w ≤ ∑ k ∈ Finset.Icc 6 22, C k

/-- Theorem 1.1 with the constant `b`: every `β` with `β ≥ 5/8 + Σ_{k=3}^{30} C_k` satisfies `β ≥ b`. -/
def BetaBoundV3At (b : ℝ) : Prop :=
  GreenFormula → VertexLemmaSeg → ∀ β : ℝ, DongCaoK30 β → b ≤ β

/-- The same for the BHH constant, with the theorem of Dong and Cao (K = 30) as a hypothesis about it. -/
def BHHBetaBoundV3At (b : ℝ) : Prop :=
  GreenFormula → VertexLemmaSeg → (∀ β : ℝ, IsBHHConstant β → DongCaoK30 β) →
    ∀ β : ℝ, IsBHHConstant β → b ≤ β

/-- Theorem 1.1 of the paper, the terms `6 ≤ k ≤ 22` at the paper's grid: `Σ_{k=6}^{22} C_k ≥ 0.0042404631`. -/
def W3Bound : Prop := W3BoundAt (42404631 / 10 ^ 10)

/-- Theorem 1.1 of the paper: `β ≥ 0.6508522354`. -/
def BetaBoundV3 : Prop := BetaBoundV3At (6508522354 / 10 ^ 10)

/-- Theorem 1.1 of the paper for the BHH constant. -/
def BHHBetaBoundV3 : Prop := BHHBetaBoundV3At (6508522354 / 10 ^ 10)

end BHH
