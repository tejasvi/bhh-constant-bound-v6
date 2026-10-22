/-
Statements of the kernel-only proof (standard axioms only), K2: the same objects and hypotheses as
`BHH/StatementV2.lean`, with the C_3 bound of the paper's tree (`3 0.1 0.0002 1e-12`, ninit 4096) and the C_4 bound of
the `4 0.4 0.002 3e-10` tree (ninit 512, chk_ck14 build 4e0b4290: CERTIFIED C_4 >= 0.0059365909, run14_k4_final.log),
hence (with `C_k ≥ 0` for `k ≥ 5`) `β ≥ 0.6426496`.
-/
import BHH.DefsV2

open scoped ENNReal

namespace BHH

/-- The kernel-only proof, K2: `C_3 ≥ 0.0117130195` and `C_4 ≥ 0.0059365909`. -/
def MainBoundsK2 : Prop :=
  GreenFormula → VertexLemmaSeg →
    ENNReal.ofReal (117130195 / 10 ^ 10) ≤ C 3 ∧
    ENNReal.ofReal (59365909 / 10 ^ 10) ≤ C 4

/-- The kernel-only proof, K2: every `β` with `β ≥ 5/8 + Σ_{k=3}^{30} C_k` satisfies `β ≥ 0.6426496`. -/
def BetaBoundK2 : Prop :=
  GreenFormula → VertexLemmaSeg → ∀ β : ℝ, DongCaoK30 β → (6426496 / 10 ^ 7 : ℝ) ≤ β

/-- The same for the BHH constant, with the theorem of Dong and Cao (K = 30) as a hypothesis about it. -/
def BHHBetaBoundK2 : Prop :=
  GreenFormula → VertexLemmaSeg → (∀ β : ℝ, IsBHHConstant β → DongCaoK30 β) →
    ∀ β : ℝ, IsBHHConstant β → (6426496 / 10 ^ 7 : ℝ) ≤ β

end BHH
