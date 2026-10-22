/-
Definitions for the lower bound on the Beardwood-Halton-Hammersley constant.

Everything in this file is a definition; nothing is assumed.  The two geometric facts that are not
formalized (Green's formula for a union of unit disks, and the vertex lemma of the paper) are stated
here as `Prop`-valued definitions and appear as explicit hypotheses of the main theorems
(the `BHH/Statement*.lean` files).  So does the theorem of Dong and Cao (with the BHH theorem behind it).

Indexing: the points are `y 0, ..., y (k-1)` (the paper writes `y_1, ..., y_k`); `y 0 = 0`.
-/
import Mathlib

open MeasureTheory Set Real
open scoped ENNReal

noncomputable section

namespace BHH

/-! ## The plane, disks, areas -/

/-- A point of the plane.  `ℝ × ℝ` carries the product Lebesgue measure `volume` (planar area). -/
abbrev Pt := ℝ × ℝ

/-- Squared Euclidean distance. -/
def sqDist (a b : Pt) : ℝ := (a.1 - b.1) ^ 2 + (a.2 - b.2) ^ 2

/-- Euclidean distance. -/
def edist2 (a b : Pt) : ℝ := √(sqDist a b)

/-- Euclidean norm. -/
def enorm2 (a : Pt) : ℝ := √(a.1 ^ 2 + a.2 ^ 2)

/-- The closed disk `B(a, ρ)` for the Euclidean distance. -/
def disk (a : Pt) (ρ : ℝ) : Set Pt := {z | sqDist z a ≤ ρ ^ 2}

/-- `A(y)`: the area of the union of the closed unit disks centred at the points of `y`. -/
def unionArea {k : ℕ} (y : Fin k → Pt) : ℝ := (volume (⋃ i, disk (y i) 1)).toReal

/-! ## The unit-distance graph and Dong-Cao's function `g` -/

/-- `G_1(y)`: two points are adjacent when their distance is at most `1`. -/
def unitGraph {k : ℕ} (y : Fin k → Pt) : SimpleGraph (Fin k) where
  Adj i j := i ≠ j ∧ sqDist (y i) (y j) ≤ 1
  symm := ⟨fun i j h => ⟨h.1.symm, by
    have := h.2; unfold sqDist at this ⊢; nlinarith [this]⟩⟩
  loopless := ⟨fun i h => h.1 rfl⟩

section DongCao
variable {V : Type*} [Fintype V]

/-- Number of vertices of degree one, `n_1(G)`. -/
def n1 (G : SimpleGraph V) : ℕ := by
  classical exact (Finset.univ.filter fun v => G.degree v = 1).card

/-- `D(G) = (1/2) Σ_v (2 - d_G(v))_+` (Dong-Cao, Definition 5). -/
def dcD (G : SimpleGraph V) : ℝ := by
  classical exact (1 / 2 : ℝ) * ∑ v, max (2 - (G.degree v : ℝ)) 0

/-- `cc(G - S)`: the number of connected components of the subgraph induced by `V \ S`
(it is `0` when `S = V`). -/
def ccDel (G : SimpleGraph V) (S : Finset V) : ℕ :=
  Nat.card (G.induce ((S : Set V)ᶜ)).ConnectedComponent

/-- `q(G) = max {1, ⌈n_1/2⌉, max_S (cc(G - S) - |S|)}` (Dong-Cao, Definition 5). -/
def dcQ (G : SimpleGraph V) : ℤ :=
  max (max 1 ⌈(n1 G : ℝ) / 2⌉)
    ((Finset.univ : Finset (Finset V)).sup' Finset.univ_nonempty
      fun S => (ccDel G S : ℤ) - S.card)

/-- Dong-Cao's `g`: `q(G) - D(G)` for connected `G`, and `0` for disconnected `G`. -/
def dcG (G : SimpleGraph V) : ℝ := by
  classical exact if G.Connected then (dcQ G : ℝ) - dcD G else 0

end DongCao

/-! ## The integrals `C_k` -/

/-- The configuration `(0, z_0, ..., z_{m-1})`: the first point is the origin. -/
def cfg {m : ℕ} (z : Fin m → Pt) : Fin (m + 1) → Pt := Fin.cons (0 : Pt) z

/-- The integrand of `C_k` (with `k = m + 1` points): `g(G_1(y)) A(y)^{-(k - 1/2)}`. -/
def ckIntegrand (m : ℕ) (z : Fin m → Pt) : ℝ :=
  dcG (unitGraph (cfg z)) * unionArea (cfg z) ^ (-((m + 1 : ℝ) - 1 / 2))

/-- Dong-Cao's `C_k = Γ(k - 1/2)/(2 k!) ∫_{(ℝ²)^{k-1}} g(G_1(y)) A(y)^{-(k-1/2)} dy_2 ⋯ dy_k`, `y_1 = 0`,
as a Lebesgue integral in `[0, ∞]` (the integrand is nonnegative). -/
def C (k : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.Gamma ((k : ℝ) - 1 / 2) / (2 * (k.factorial : ℝ))) *
    ∫⁻ z : Fin (k - 1) → Pt, ENNReal.ofReal (ckIntegrand (k - 1) z)

/-! ## The BHH constant and the theorem of Dong and Cao (hypotheses, not proved here) -/

/-- Length of the shortest closed tour through the points `x 0, ..., x (n-1)`. -/
def tourLength {n : ℕ} (x : Fin n → Pt) : ℝ :=
  ⨅ σ : Equiv.Perm (Fin n), ∑ i : Fin n,
    edist2 (x (σ i)) (x (σ (finRotate n i)))

/-- The unit square `[0,1]²`. -/
def unitSquare : Set Pt := Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1

/-- `β` is the constant of the Beardwood-Halton-Hammersley theorem: for independent uniform random
points `X_0, X_1, ...` of the unit square, `L_n / √n → β` almost surely, where `L_n` is the length of
the shortest tour through `X_0, ..., X_{n-1}`. -/
def IsBHHConstant (β : ℝ) : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → Pt),
    (∀ i, Measurable (X i)) → ProbabilityTheory.iIndepFun X P →
    (∀ i, P.map (X i) = (volume.restrict unitSquare)) →
    ∀ᵐ ω ∂P, Filter.Tendsto (fun n : ℕ => tourLength (fun i : Fin n => X i ω) / √(n : ℝ))
      Filter.atTop (nhds β)

/-- Dong and Cao (arXiv:2610.02809v1, Theorem 3) with `K = 5`: `β ≥ 5/8 + C_3 + C_4 + C_5`. -/
def DongCaoK5 (β : ℝ) : Prop :=
  (5 / 8 : ℝ≥0∞) + (C 3 + C 4 + C 5) ≤ ENNReal.ofReal β

/-! ## Green's formula for the union of unit disks (hypothesis, paper eq. (2.1)) -/

/-- The direction `u(t) = (cos t, sin t)`. -/
def dir (t : ℝ) : Pt := (Real.cos t, Real.sin t)

/-- `E_i(y)`: the directions `t ∈ [0, 2π)` such that `y_i + u(t)` lies in no open unit disk
`B°(y_j, 1)`, `j ≠ i` (the exposed part of the circle around `y_i`). -/
def exposed {k : ℕ} (y : Fin k → Pt) (i : Fin k) : Set ℝ :=
  {t | t ∈ Ico 0 (2 * π) ∧ ∀ j, j ≠ i → 1 ≤ sqDist (y i + dir t) (y j)}

/-- The right-hand side of Green's formula, `(1/2) Σ_i ∫_{E_i} (1 + ⟨y_i, u(t)⟩) dt`. -/
def greenArea {k : ℕ} (y : Fin k → Pt) : ℝ :=
  (1 / 2 : ℝ) * ∑ i, ∫ t in exposed y i, (1 + (y i).1 * Real.cos t + (y i).2 * Real.sin t)

/-- The gradient formula (paper eq. (2.2)): `∇_{y_i} A(y) = ∫_{E_i(y)} u(t) dt`. -/
def greenGrad {k : ℕ} (y : Fin k → Pt) (i : Fin k) : Pt :=
  (∫ t in exposed y i, Real.cos t, ∫ t in exposed y i, Real.sin t)

/-- Green's formula (paper eq. (2.1)) for configurations of distinct points. -/
def GreenFormula : Prop :=
  ∀ (k : ℕ) (y : Fin k → Pt), (∀ i j, i ≠ j → y i ≠ y j) → unionArea y = greenArea y

/-! ## The vertex lemma (hypothesis, paper Lemma 3.1 with Remark 3.2 and eq. (2.2)) -/

/-- An axis-parallel rectangle `[xl, xh] × [yl, yh]` (possibly degenerate). -/
structure Rect where
  xl : ℝ
  xh : ℝ
  yl : ℝ
  yh : ℝ

namespace Rect

/-- Membership in the closed rectangle. -/
def Mem (R : Rect) (p : Pt) : Prop := R.xl ≤ p.1 ∧ p.1 ≤ R.xh ∧ R.yl ≤ p.2 ∧ p.2 ≤ R.yh

/-- The centre `c` of the rectangle. -/
def centre (R : Rect) : Pt := ((R.xl + R.xh) / 2, (R.yl + R.yh) / 2)

/-- `ε`: half the diagonal, the largest distance from the centre. -/
def eps (R : Rect) : ℝ := √((R.xh - R.xl) ^ 2 + (R.yh - R.yl) ^ 2) / 2

end Rect

/-- Least distance `|x - y|` for `x ∈ [a, b]`, `y ∈ [c, d]`. -/
def gap (a b c d : ℝ) : ℝ := max (max (c - b) (a - d)) 0

/-- Largest distance `|x - y|` for `x ∈ [a, b]`, `y ∈ [c, d]`. -/
def span (a b c d : ℝ) : ℝ := max |d - a| |b - c|

/-- `(d^-)^2`: squared least distance between two rectangles. -/
def dminSq (R S : Rect) : ℝ := gap R.xl R.xh S.xl S.xh ^ 2 + gap R.yl R.yh S.yl S.yh ^ 2

/-- `(d^+)^2`: squared largest distance between two rectangles. -/
def dmaxSq (R S : Rect) : ℝ := span R.xl R.xh S.xl S.xh ^ 2 + span R.yl R.yh S.yl S.yh ^ 2

/-- `T_ij(w) = λ w + μ + min(w/d^-, π)` (paper eq. (3.3)); `first = true` selects
`(λ, μ) = (1/√(4 - (d^+)^2), 0)` (allowed only when `d^+ < 2`), `first = false` selects
`(λ, μ) = (0, 2 arcsin(min(d^+, 2)/2) - 2 arcsin(d^- / 2))`. -/
def Tbound (R S : Rect) (first : Bool) (w : ℝ) : ℝ :=
  (if first then w / √(4 - dmaxSq R S)
    else 2 * Real.arcsin (min (√(dmaxSq R S)) 2 / 2) - 2 * Real.arcsin (√(dminSq R S) / 2))
  + min (w / √(dminSq R S)) π

/-- The two intersection points of the unit circles around `a` and `b` (for `0 < |a - b| < 2`). -/
def vertexPts (a b : Pt) : Pt × Pt :=
  let w : Pt := b - a
  let dc := enorm2 w
  let s := √(1 - dc ^ 2 / 4) / dc
  (a + (1 / 2 : ℝ) • w + s • ((-w.2, w.1) : Pt), a + (1 / 2 : ℝ) • w - s • ((-w.2, w.1) : Pt))

/-- Remark 3.2: the vertex `P` of the pair `ij` (at the centre configuration) is certified covered
on the box if `|P - c_l| + ε_i + T_ij(ε_i + ε_j) + ε_l < 1` for some `l ∉ {i, j}`. -/
def certCovered {k : ℕ} (R : Fin k → Rect) (first : Fin k → Fin k → Bool) (i j : Fin k) (P : Pt) :
    Prop :=
  ∃ l, l ≠ i ∧ l ≠ j ∧
    edist2 P (R l).centre + (R i).eps + Tbound (R i) (R j) (first i j) ((R i).eps + (R j).eps)
      + (R l).eps < 1

/-- `ν_ij`: the number of vertices of the pair `ij` that are not certified covered (`2` when the
circles around the centres do not meet in two points). -/
def nuCount {k : ℕ} (R : Fin k → Rect) (first : Fin k → Fin k → Bool) (i j : Fin k) : ℕ := by
  classical exact
    let dc := edist2 (R i).centre (R j).centre
    if 0 < dc ∧ dc < 2 then
      (if certCovered R first i j (vertexPts (R i).centre (R j).centre).1 then 0 else 1) +
      (if certCovered R first i j (vertexPts (R i).centre (R j).centre).2 then 0 else 1)
    else 2

/-- The vertex remainder `ϱ(δ) = Σ_{i<j, d^-_ij<2} ν_ij (|δ_i| + |δ_j|) T_ij(|δ_j - δ_i|)`,
`δ_i = y_i - c_i`. -/
def vertexRem {k : ℕ} (R : Fin k → Rect) (first : Fin k → Fin k → Bool) (y : Fin k → Pt) : ℝ := by
  classical exact
    ∑ i, ∑ j, if i < j ∧ dminSq (R i) (R j) < 4 then
      (nuCount R first i j : ℝ) *
        (enorm2 (y i - (R i).centre) + enorm2 (y j - (R j).centre)) *
        Tbound (R i) (R j) (first i j) (enorm2 ((y j - (R j).centre) - (y i - (R i).centre)))
    else 0

/-- The vertex lemma (paper Lemma 3.1 with the pruning test of Remark 3.2, and the gradient
formula (2.2)): for rectangles `R_i` with `d^-_ij > 0` for all `i ≠ j`, every configuration `y` with
`y_i ∈ R_i` satisfies `|A(y) - A(c) - Σ_i ⟨∇_{y_i} A(c), y_i - c_i⟩| ≤ ϱ(y - c)`, where `c` is the
configuration of the centres and `∇_{y_i} A(c) = ∫_{E_i(c)} u(t) dt`. -/
def VertexLemma : Prop :=
  ∀ (k : ℕ) (R : Fin k → Rect) (first : Fin k → Fin k → Bool),
    (∀ i j, i ≠ j → 0 < dminSq (R i) (R j)) →
    (∀ i j, first i j = true → dmaxSq (R i) (R j) < 4) →
    ∀ y : Fin k → Pt, (∀ i, (R i).Mem (y i)) →
      |unionArea y - unionArea (fun i => (R i).centre)
          - ∑ i, ((greenGrad (fun i => (R i).centre) i).1 * (y i - (R i).centre).1
                 + (greenGrad (fun i => (R i).centre) i).2 * (y i - (R i).centre).2)|
        ≤ vertexRem R first y

end BHH
