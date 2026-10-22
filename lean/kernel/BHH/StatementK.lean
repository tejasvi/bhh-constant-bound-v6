/-
Statements of the kernel-only proof (standard axioms only): the same objects and hypotheses as
`BHH/StatementV2.lean`, with the bounds for `C_3`, `C_4` that the kernel-checked trees reach.

K1 (reduced trees `3 0.1 0.0005 1e-10` and `4 0.4 0.01 3e-9`): `C_3 ≥ 0.0117028397`, `C_4 ≥ 0.0054272702`,
hence (with `C_k ≥ 0` for `k ≥ 5`) `β ≥ 0.6421301` (Dong and Cao: `β ≥ 0.6421`).
-/
import BHH.DefsV2

open scoped ENNReal

namespace BHH

/-- The kernel-only proof, K1: `C_3 ≥ 0.0117028397` and `C_4 ≥ 0.0054272702`. -/
def MainBoundsK1 : Prop :=
  GreenFormula → VertexLemmaSeg →
    ENNReal.ofReal (117028397 / 10 ^ 10) ≤ C 3 ∧
    ENNReal.ofReal (54272702 / 10 ^ 10) ≤ C 4

/-- The kernel-only proof, K1: every `β` with `β ≥ 5/8 + Σ_{k=3}^{30} C_k` satisfies `β ≥ 0.6421301`. -/
def BetaBoundK1 : Prop :=
  GreenFormula → VertexLemmaSeg → ∀ β : ℝ, DongCaoK30 β → (6421301 / 10 ^ 7 : ℝ) ≤ β

/-- The same for the BHH constant, with the theorem of Dong and Cao (K = 30) as a hypothesis about it. -/
def BHHBetaBoundK1 : Prop :=
  GreenFormula → VertexLemmaSeg → (∀ β : ℝ, IsBHHConstant β → DongCaoK30 β) →
    ∀ β : ℝ, IsBHHConstant β → (6421301 / 10 ^ 7 : ℝ) ≤ β

end BHH
