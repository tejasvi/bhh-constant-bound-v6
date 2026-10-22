/-
The statements of the native bound (beta >= 0.6491725104), as `Prop`-valued definitions.

Hypotheses: `GreenFormula` (paper eq. (2.1)), `VertexLemmaSeg` (paper Lemma 3.1 with Remark 3.2 and eq. (2.2), along a
segment) and Dong-Cao's Theorem 3 with `K = 30` (`DongCaoK30`, resting on the BHH theorem).  Nothing else is assumed.
Box part (k = 3, 4, 5): `BHH/`.  Window-2 part (6 <= k <= 30): `W2/`
(`W2Bound`).
-/
import BHH.DefsV2

open scoped ENNReal

namespace BHH

/-- The native bound, the terms `k = 3, 4, 5`: `C_3 ≥ 0.0117130195`, `C_4 ≥ 0.0063707166`,
`C_5 ≥ 0.0034034701`. -/
def MainBoundsV2 : Prop :=
  GreenFormula → VertexLemmaSeg →
    ENNReal.ofReal (117130195 / 10 ^ 10) ≤ C 3 ∧
    ENNReal.ofReal (63707166 / 10 ^ 10) ≤ C 4 ∧
    ENNReal.ofReal (34034701 / 10 ^ 10) ≤ C 5

/-- The native bound, the terms `6 ≤ k ≤ 30`: `Σ_{k=6}^{30} C_k ≥ 0.0026853042`. -/
def W2Bound : Prop :=
  GreenFormula → VertexLemmaSeg →
    ENNReal.ofReal (26853042 / 10 ^ 10) ≤ ∑ k ∈ Finset.Icc 6 30, C k

/-- The native bound: every `β` with `β ≥ 5/8 + Σ_{k=3}^{30} C_k` satisfies `β ≥ 0.6491725104`. -/
def BetaBoundV2 : Prop :=
  GreenFormula → VertexLemmaSeg → ∀ β : ℝ, DongCaoK30 β → (6491725104 / 10 ^ 10 : ℝ) ≤ β

/-- The same for the BHH constant, with the theorem of Dong and Cao (K = 30) as a hypothesis about it. -/
def BHHBetaBoundV2 : Prop :=
  GreenFormula → VertexLemmaSeg → (∀ β : ℝ, IsBHHConstant β → DongCaoK30 β) →
    ∀ β : ℝ, IsBHHConstant β → (6491725104 / 10 ^ 10 : ℝ) ≤ β

/-- Sanity statement (not a hypothesis of anything): every `C_k`, `k ≥ 3`, is finite, so `MainBoundsV2` and
`W2Bound` cannot hold because some `C_k = ∞`, and `DongCaoK30` is satisfiable. -/
def CFinite : Prop := ∀ k : ℕ, 3 ≤ k → C k < ⊤

end BHH
