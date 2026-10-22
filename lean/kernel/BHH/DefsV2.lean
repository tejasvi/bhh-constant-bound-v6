/-
Shared definitions for version 2 of the paper, used by the box part (`BHH/`) and the window-2 part (`W2/`).
Definitions only.

* `VertexLemmaSeg`: the vertex lemma (paper Lemma 3.1 with Remark 3.2 and eq. (2.2)) along the segment from an
  expansion point `c` to a configuration `y` (the paper's proof uses only this segment).  It replaces the rectangle form
  `VertexLemma` of `BHH/Defs.lean` as the hypothesis of the v2 statements (`VertexLemmaSeg → VertexLemma` is a lemma).
* `DongCaoK30`: Dong-Cao Theorem 3 with `K = 30`.

The definitions of `Tseg`, `segPt`, `certCoveredSeg`, `nuCountSeg`, `vertexRemSeg`, `VertexLemmaSeg`, `DongCaoK30`
are shared by the box part and the window-2 part.
-/
import BHH.Defs

open MeasureTheory Set Real
open scoped ENNReal

noncomputable section

namespace BHH

/-! ## The vertex lemma along a segment (hypothesis) -/

/-- `T(w) = λ w + μ + min(w/d⁻, π)` (paper eq. (3.3)) for distance bounds `dlo = d⁻`, `dhi = d⁺`; `first = true`
selects `(λ, μ) = (1/√(4 - (d⁺)^2), 0)` (allowed only when `d⁺ < 2`), `first = false` selects
`(λ, μ) = (0, 2 arcsin(min(d⁺, 2)/2) - 2 arcsin(d⁻/2))`. -/
def Tseg (dlo dhi : ℝ) (first : Bool) (w : ℝ) : ℝ :=
  (if first then w / √(4 - dhi ^ 2)
    else 2 * Real.arcsin (min dhi 2 / 2) - 2 * Real.arcsin (dlo / 2))
  + min (w / dlo) π

/-- The point `c + t (y - c)` of the segment from `c` to `y`. -/
def segPt (c y : Pt) (t : ℝ) : Pt := c + t • (y - c)

/-- Remark 3.2 along a segment: the vertex `P` of the pair `ij` at the expansion point `c` is certified covered if
`|P - c_l| + ε_i + T_ij(ε_i + ε_j) + ε_l < 1` for some `l ∉ {i, j}`, where `ε_i ≥ |y_i - c_i|`. -/
def certCoveredSeg {k : ℕ} (c : Fin k → Pt) (eps : Fin k → ℝ) (dlo dhi : Fin k → Fin k → ℝ)
    (first : Fin k → Fin k → Bool) (i j : Fin k) (P : Pt) : Prop :=
  ∃ l, l ≠ i ∧ l ≠ j ∧
    edist2 P (c l) + eps i + Tseg (dlo i j) (dhi i j) (first i j) (eps i + eps j) + eps l < 1

/-- `ν_ij`: the number of vertices of the pair `ij` (at `c`) that are not certified covered (`2` when the circles
around `c_i` and `c_j` do not meet in two points). -/
def nuCountSeg {k : ℕ} (c : Fin k → Pt) (eps : Fin k → ℝ) (dlo dhi : Fin k → Fin k → ℝ)
    (first : Fin k → Fin k → Bool) (i j : Fin k) : ℕ := by
  classical exact
    let dc := edist2 (c i) (c j)
    if 0 < dc ∧ dc < 2 then
      (if certCoveredSeg c eps dlo dhi first i j (vertexPts (c i) (c j)).1 then 0 else 1) +
      (if certCoveredSeg c eps dlo dhi first i j (vertexPts (c i) (c j)).2 then 0 else 1)
    else 2

/-- The vertex remainder `ϱ(δ) = Σ_{i<j, d⁻_ij<2} ν_ij (|δ_i| + |δ_j|) T_ij(|δ_j - δ_i|)`, `δ_i = y_i - c_i`. -/
def vertexRemSeg {k : ℕ} (c y : Fin k → Pt) (eps : Fin k → ℝ) (dlo dhi : Fin k → Fin k → ℝ)
    (first : Fin k → Fin k → Bool) : ℝ := by
  classical exact
    ∑ i, ∑ j, if i < j ∧ dlo i j < 2 then
      (nuCountSeg c eps dlo dhi first i j : ℝ) * (enorm2 (y i - c i) + enorm2 (y j - c j)) *
        Tseg (dlo i j) (dhi i j) (first i j) (enorm2 ((y j - c j) - (y i - c i)))
    else 0

/-- The vertex lemma along a segment (paper Lemma 3.1 with Remark 3.2 and eq. (2.2); its proof uses only the segment
from the expansion point `c` to `y`): if along `y(t) = c + t (y - c)`, `t ∈ [0, 1]`, every pair distance satisfies
`0 < d⁻_ij ≤ |y_i(t) - y_j(t)| ≤ d⁺_ij`, and `|y_i - c_i| ≤ ε_i`, then
`|A(y) - A(c) - Σ_i ⟨∇_{y_i} A(c), y_i - c_i⟩| ≤ ϱ(y - c)`, with `∇_{y_i} A(c) = ∫_{E_i(c)} u(t) dt`. -/
def VertexLemmaSeg : Prop :=
  ∀ (k : ℕ) (c y : Fin k → Pt) (eps : Fin k → ℝ) (dlo dhi : Fin k → Fin k → ℝ)
    (first : Fin k → Fin k → Bool),
    (∀ i j, i < j → 0 < dlo i j) →
    (∀ i j, i < j → ∀ t ∈ Icc (0 : ℝ) 1,
        dlo i j ≤ edist2 (segPt (c i) (y i) t) (segPt (c j) (y j) t) ∧
        edist2 (segPt (c i) (y i) t) (segPt (c j) (y j) t) ≤ dhi i j) →
    (∀ i j, i < j → first i j = true → dhi i j < 2) →
    (∀ i, enorm2 (y i - c i) ≤ eps i) →
    |unionArea y - unionArea c
        - ∑ i, ((greenGrad c i).1 * (y i - c i).1 + (greenGrad c i).2 * (y i - c i).2)|
      ≤ vertexRemSeg c y eps dlo dhi first

/-- Dong and Cao (arXiv:2610.02809v1, Theorem 3) with `K = 30`: `β ≥ 5/8 + Σ_{k=3}^{30} C_k`. -/
def DongCaoK30 (β : ℝ) : Prop :=
  (5 / 8 : ℝ≥0∞) + ∑ k ∈ Finset.Icc 3 30, C k ≤ ENNReal.ofReal β

end BHH
