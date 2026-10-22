/-
Module D: statements of the three leaf branches delegated to helpers (definitions only).

* `Prop38Spec`   the Prop 3.8 branch (some pair with `d⁻ = 0`), pointwise
* `StraddleSpec` one straddling pair (Prop 3.7 with Lemma 3.5)
* `ExtraSpec`    the interior term plus the extra terms of Prop 3.6 (one or two undetermined edges)

The real integrand is abstract (`f`, with lower/upper bounds on the box and an integral lower bound); the top level
instantiates `f x = ofReal (r_2 φ(A(y)))`, so that `F2 k x = ofReal (2 g(G(y))) · f x`.
-/
import BHH.LeafSound.LeafAlt
import BHH.LeafSound.BoxState
import BHH.Box.Props

open BHH.Cert Real MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace BHH

/-- Prop 3.8 branch, pointwise: if the union of the enlarged disks at the distinct centres is enclosed by `u`, every
point of the box has `F2 ≥ r_2^- · gmin · φ(A^+)` (rounded down, clipped at 0). -/
def Prop38Spec (k : ℕ) (gt : GTab) (cs : ℤ → Iv × Iv) (cand : CandFn) : Prop :=
  ∀ lo hi : List ℤ, ValidBox k lo hi →
    0 < listGet lo 0 → 0 < gt.gmin (val3 (stCode k lo hi)) →
    ∀ u : UnionRes,
      BHH.Cert.unionArea cs (distinctOf ((ptBoxes k lo hi).map fun P => (P.xc, P.yc)))
        (ONE + deltaOf (ptBoxes k lo hi)) cand = some u →
      ∀ x ∈ (boxOf lo hi : Set (Fin (mDim k) → ℝ)),
        ENNReal.ofReal (fx (max (p38lb k u (listGet lo 0) (gt.gmin (val3 (stCode k lo hi)))) 0)) ≤ F2 k x

/-- One straddling pair `(j, j+1)` (the other ordered pairs in order, `r_2, η_2 ≥ 0` on the box): with `f` between
`fmin` and `fmax` on the box and `∫_box f ≥ vol · val`, the code's straddle term is a lower bound of
`∫_{box ∩ D_k} 2g f`. -/
def StraddleSpec (k : ℕ) (gt : GTab) : Prop :=
  ∀ lo hi : List ℤ, ValidBox k lo hi → ∀ j : ℕ, 2 ≤ j → j + 1 < k →
    0 ≤ lo.getD 0 0 → (2 < k → 0 ≤ lo.getD 2 0) →
    (∀ j', 2 ≤ j' → j' + 1 < k → j' ≠ j → hi.getD (2 * j' - 3) 0 ≤ lo.getD (2 * (j' + 1) - 3) 0) →
    ∀ f : (Fin (mDim k) → ℝ) → ℝ≥0∞,
    ∀ fminLo fmaxHi val : ℤ, 0 ≤ fminLo → 0 ≤ fmaxHi → 0 ≤ val →
      (∀ x ∈ (boxOf lo hi : Set (Fin (mDim k) → ℝ)), ENNReal.ofReal (fx fminLo) ≤ f x) →
      (∀ x ∈ (boxOf lo hi : Set (Fin (mDim k) → ℝ)), f x ≤ ENNReal.ofReal (fx fmaxHi)) →
      ENNReal.ofReal ((volume (boxOf lo hi : Set (Fin (mDim k) → ℝ))).toReal * fx val) ≤
        ∫⁻ x in boxOf lo hi, f x →
      0 ≤ gt.gmin (val3 (stCode k lo hi)) →
      let P := (ptBoxes k lo hi).getD j default
      let Q := (ptBoxes k lo hi).getD (j + 1) default
      let pord := max (cdfIv P.xl P.xh Q.xl Q.xh 0).lo 0
      ENNReal.ofReal ((volume (boxOf lo hi : Set (Fin (mDim k) → ℝ))).toReal *
          fx (gt.gmin (val3 (stCode k lo hi)) * evLB pord fminLo fmaxHi val)) ≤
        ∫⁻ x in boxOf lo hi ∩ Dk k, ENNReal.ofReal (2 * dcG (unitGraph (xcfg k x))) * f x

/-- Interior term plus the extra terms of Prop 3.6 (no straddling pair: the box lies in `D_k`): with `f` between
`fmin` and `fmax` on the box and `∫_box f ≥ vol · val`, `vol · (gmin · val + max(single, pairs))` is a lower bound of
`∫_box 2g f`. -/
def ExtraSpec (k : ℕ) (gt : GTab) : Prop :=
  ∀ lo hi : List ℤ, ValidBox k lo hi →
    ∀ f : (Fin (mDim k) → ℝ) → ℝ≥0∞,
    ∀ fminLo fmaxHi val : ℤ, 0 ≤ fminLo → 0 ≤ fmaxHi → 0 ≤ val →
      (∀ x ∈ (boxOf lo hi : Set (Fin (mDim k) → ℝ)), ENNReal.ofReal (fx fminLo) ≤ f x) →
      (∀ x ∈ (boxOf lo hi : Set (Fin (mDim k) → ℝ)), f x ≤ ENNReal.ofReal (fx fmaxHi)) →
      ENNReal.ofReal ((volume (boxOf lo hi : Set (Fin (mDim k) → ℝ))).toReal * fx val) ≤
        ∫⁻ x in boxOf lo hi, f x →
      0 ≤ gt.gmin (val3 (stCode k lo hi)) →
      let idx3 := val3 (stCode k lo hi)
      let gmin := gt.gmin idx3
      let probs := probsOf (ptBoxes k lo hi) (pairList k) (stCode k lo hi)
      ENNReal.ofReal ((volume (boxOf lo hi : Set (Fin (mDim k) → ℝ))).toReal *
          ((gmin : ℝ) * fx val + fx (max (singleLB gt idx3 gmin probs fminLo fmaxHi val)
            (pairsLB gt idx3 gmin probs fminLo fmaxHi val)))) ≤
        ∫⁻ x in boxOf lo hi, ENNReal.ofReal (2 * dcG (unitGraph (xcfg k x))) * f x

end BHH
