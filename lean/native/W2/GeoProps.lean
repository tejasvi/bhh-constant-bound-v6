/-
Geometric facts about polar sectors used by the table soundness (paper Section 4.4: cell areas, the radial
Riemann sums of `E A_1`, centroids and second moments, the hull of a cell for the vertex lemma, and the bound
`|∇_{y_i} A| ≤ 2`), as named `Prop`s for separate proof modules.  Definitions only.

The cells of the grid are sectors: `g.cell ir it = sector (g.rad ir) (g.rad (ir + 1)) (g.ang it) (g.ang (it + 1))`
(by `rfl`).  The table code works with the rotated cells at angles `(0, dθ)` and `(d dθ, (d + 1) dθ)`, so the facts
are stated for general sectors with `-π ≤ a < b ≤ π`, `b - a ≤ π/2`.
-/
import W2.Defs
import BHH.DefsV2

open MeasureTheory Set Real
open scoped ENNReal

noncomputable section

namespace BHH.W2

/-- The open polar sector `{ρ u(φ) : r1 < ρ < r2, a < φ < b}`. -/
def sector (r1 r2 a b : ℝ) : Set Pt := polarCoord.symm '' (Ioo r1 r2 ×ˢ Ioo a b)

/-- Admissible sector parameters: `0 ≤ r1 < r2`, `-π ≤ a < b ≤ π`, `b - a ≤ π/2`. -/
def SecOK (r1 r2 a b : ℝ) : Prop := 0 ≤ r1 ∧ r1 < r2 ∧ -π ≤ a ∧ a < b ∧ b ≤ π ∧ b - a ≤ π / 2

/-- The centroid radius `(2/3) (r2³ - r1³)/(r2² - r1²) · sin h / h`, `h = (b - a)/2`. -/
def secRho (r1 r2 a b : ℝ) : ℝ :=
  2 / 3 * ((r2 ^ 3 - r1 ^ 3) / (r2 ^ 2 - r1 ^ 2)) * (Real.sin ((b - a) / 2) / ((b - a) / 2))

/-- The centroid `secRho · u((a + b)/2)` of the sector. -/
def secCentroid (r1 r2 a b : ℝ) : Pt :=
  (secRho r1 r2 a b * Real.cos ((a + b) / 2), secRho r1 r2 a b * Real.sin ((a + b) / 2))

/-- (G1) The area of a sector: `(r2² - r1²)(b - a)/2`. -/
def SectorArea : Prop :=
  ∀ r1 r2 a b : ℝ, SecOK r1 r2 a b →
    volume (sector r1 r2 a b) = ENNReal.ofReal ((r2 ^ 2 - r1 ^ 2) * (b - a) / 2)

/-- (G2) Radial integrals over a sector: `∫_S f(|z|) dz = (b - a) ∫_{r1}^{r2} f(r) r dr`. -/
def SectorRadial : Prop :=
  ∀ (r1 r2 a b : ℝ) (f : ℝ → ℝ), SecOK r1 r2 a b → ContinuousOn f (Icc r1 r2) →
    ∫ z in sector r1 r2 a b, f (enorm2 z) = (b - a) * ∫ r in r1..r2, f r * r

/-- (G3) First and second moments of a sector (the centroid is `secCentroid`, by `sin b - sin a =
2 cos((a+b)/2) sin((b-a)/2)` and `cos a - cos b = 2 sin((a+b)/2) sin((b-a)/2)`). -/
def SectorMoments : Prop :=
  ∀ r1 r2 a b : ℝ, SecOK r1 r2 a b →
    (∫ z in sector r1 r2 a b, z.1) = (r2 ^ 3 - r1 ^ 3) / 3 * (Real.sin b - Real.sin a) ∧
    (∫ z in sector r1 r2 a b, z.2) = (r2 ^ 3 - r1 ^ 3) / 3 * (Real.cos a - Real.cos b) ∧
    (∫ z in sector r1 r2 a b, (z.1 ^ 2 + z.2 ^ 2)) = (r2 ^ 4 - r1 ^ 4) / 4 * (b - a)

/-- (G4) The hull of a sector, as used by the vertex lemma: every point of a segment from the centroid to a point of
the sector is `ρ u(φ)` with `r1 cos((b - a)/2) ≤ ρ ≤ r2` and `a ≤ φ ≤ b`.  (The set
`{x : ⟨x, n_a⟩ ≥ 0, ⟨x, n_b⟩ ≥ 0, |x| ≤ r2, ⟨x, u((a+b)/2)⟩ ≥ r1 cos((b-a)/2)}` is convex, contains the sector and
the centroid, and lies in that polar box.) -/
def SectorHull : Prop :=
  ∀ r1 r2 a b : ℝ, SecOK r1 r2 a b → ∀ z ∈ sector r1 r2 a b, ∀ s ∈ Icc (0 : ℝ) 1,
    ∃ ρ φ : ℝ, segPt (secCentroid r1 r2 a b) z s = (ρ * Real.cos φ, ρ * Real.sin φ) ∧
      r1 * Real.cos ((b - a) / 2) ≤ ρ ∧ ρ ≤ r2 ∧ a ≤ φ ∧ φ ≤ b

/-- (G5) `|∫_E u(t) dt| ≤ 2` for the exposed set `E` of any centre (the gradient formula (2.2) bounded). -/
def GreenGradLe : Prop :=
  ∀ (k : ℕ) (y : Fin k → Pt) (i : Fin k), (greenGrad y i).1 ^ 2 + (greenGrad y i).2 ^ 2 ≤ 4

/-- (G6) Lemma 4 over the reals: for `r ∈ [r1, r2]`, `q ∈ [q1, q2]` (`r1, q1 ≥ 0`), `c ∈ [c1, c2] ⊆ [-1, 1]`,
`f = r² + q² + 2 r q c` is at most its largest corner value at `c2` and at least the least of the corner values at
`c1` and, when `c1 < 0`, of the edge minima `x²(1 - c1²)` of the edges `r = x` (`x ∈ {r1, r2}`, if
`-c1 x ∈ [q1, q2]`) and `q = x` (`x ∈ {q1, q2}`, if `-c1 x ∈ [r1, r2]`). -/
def QuadBox : Prop :=
  ∀ r1 r2 q1 q2 c1 c2 r q c : ℝ, 0 ≤ r1 → 0 ≤ q1 → -1 ≤ c1 → c2 ≤ 1 →
    r1 ≤ r → r ≤ r2 → q1 ≤ q → q ≤ q2 → c1 ≤ c → c ≤ c2 →
    let f := fun (x y z : ℝ) => x ^ 2 + y ^ 2 + 2 * x * y * z
    (f r q c ≤ max (max (f r1 q1 c2) (f r1 q2 c2)) (max (f r2 q1 c2) (f r2 q2 c2))) ∧
    (∃ v, (v = f r1 q1 c1 ∨ v = f r1 q2 c1 ∨ v = f r2 q1 c1 ∨ v = f r2 q2 c1 ∨
        (c1 < 0 ∧ ((v = r1 ^ 2 * (1 - c1 ^ 2) ∧ q1 ≤ -c1 * r1 ∧ -c1 * r1 ≤ q2) ∨
                   (v = q1 ^ 2 * (1 - c1 ^ 2) ∧ r1 ≤ -c1 * q1 ∧ -c1 * q1 ≤ r2)))) ∧ v ≤ f r q c)

end BHH.W2
