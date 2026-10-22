/-
Soundness of the table computation (`W2Cert/Table.lean`) and the integrated vertex lemma, as named `Prop`s for
separate proof modules (paper Section 4.4).  Definitions only.

* T1 `RingSound`: the per-ring data `mkRing` (radii, area, centroid radius, second moment, the Riemann sums of the
  mean of `A_1`, the flag `r2 ≤ 1`).
* T2 `AngleSound`, `AngleRange`: the angle data `mkAData`, `mkDData` and the range of `cos` between two cells.
* T3 `FrangeSound`: Lemma 4 in interval arithmetic (`frange`).
* T4 `DistSound`: `distHi`, `epsCell`, `vertexDistHi`.
* T5 `A1Radial`, `A2Union`, `A2LeA1`: `A_1`, `A_2` through union areas.
* T6 `PairMean`: the vertex lemma (along segments) integrated over a product of two cells.
* T7 `RotA2`: rotating both cells of a pair does not change the integral of `A_2`.
* T8 `SectorCen`: the centroid and the second moment of a sector.

Cells are the sectors of `W2/GeoProps.lean`; the table entry of `(ir, ir2, d)` is computed for the z-cell at angles
`(0, h)` and the z'-cell at `(d h, (d + 1) h)`, `h = π / NT`.
-/
import W2.GeoProps
import W2.Unroll
import W2Cert.Table

open MeasureTheory Set Real
open scoped ENNReal

noncomputable section

namespace BHH.W2

open W2C BHH.Cert BHH

/-! ## T1: rings -/

/-- The mean of `A_1(|z|)` over the annulus `r1 < |z| < r2` (radial density `∝ r`). -/
def meanA1 (r1 r2 : ℝ) : ℝ := 2 / (r2 ^ 2 - r1 ^ 2) * ∫ r in r1..r2, A1c r * r

/-- T1: the per-ring data of ring `j` (radii `r_j < r_{j+1}`, angular width `h = π/NT`), when the interval
denominators `r_{j+1}² - r_j²` and `h/2` have positive lower ends (else `Iv.div` falls back to `[-1, 1]`). -/
def RingSound : Prop :=
  ∀ g : W2C.Grid, 0 < g.N1 → 0 < g.N2 → 2 ≤ g.NT → 0 < g.NSUB → ∀ j, j < g.NR →
    0 < (Iv.sub (Iv.sqr (radIv g (j + 1))) (Iv.sqr (radIv g j))).lo → 0 < (Iv.div2e (dthIv g) 1).lo →
    ivMem ((gR g).rad j) (mkRing g j).r1 ∧ ivMem ((gR g).rad (j + 1)) (mkRing g j).r2 ∧
    fx (mkRing g j).areaLo ≤ ((gR g).rad (j + 1) ^ 2 - (gR g).rad j ^ 2) * (π / g.NT) / 2 ∧
    ivMem (secRho ((gR g).rad j) ((gR g).rad (j + 1)) 0 (π / g.NT)) (mkRing g j).rhoc ∧
    ((gR g).rad j ^ 2 + (gR g).rad (j + 1) ^ 2) / 2 - secRho ((gR g).rad j) ((gR g).rad (j + 1)) 0 (π / g.NT) ^ 2
      ≤ fx (mkRing g j).momHi ∧
    fx (mkRing g j).euLo ≤ meanA1 ((gR g).rad j) ((gR g).rad (j + 1)) ∧
    meanA1 ((gR g).rad j) ((gR g).rad (j + 1)) ≤ fx (mkRing g j).euHi ∧
    ((mkRing g j).nflag = true → (gR g).rad (j + 1) ≤ 1)

/-! ## T2: angles -/

/-- T2: the angle data (`h = π/NT`, `2 ≤ NT ≤ 2^30`; for huge `NT` the rounded multiples of `h` pass `π`):
`cos`, `sin` of `h/2` and of the centroid direction `(2d+1) h/2` of the z'-cell, and `cmin = cos((|d|+1) h)`,
`cmax = cos((|d|-1) h)` (`1` if `|d| ≤ 1`). -/
def AngleSound : Prop :=
  ∀ g : W2C.Grid, 2 ≤ g.NT → g.NT ≤ 2 ^ 30 →
    ivMem (Real.cos (π / g.NT / 2)) (mkAData g).ch ∧ ivMem (Real.sin (π / g.NT / 2)) (mkAData g).sh ∧
    ∀ d : ℤ, |d| < g.NT →
      ivMem (Real.cos ((2 * d + 1) * (π / g.NT) / 2)) (mkDData g d).cx ∧
      ivMem (Real.sin ((2 * d + 1) * (π / g.NT) / 2)) (mkDData g d).sy ∧
      ivMem (Real.cos ((|d| + 1) * (π / g.NT))) (mkDData g d).cmin ∧
      ivMem (if |d| ≤ 1 then 1 else Real.cos ((|d| - 1) * (π / g.NT))) (mkDData g d).cmax

/-- T2: the angle between a point of the closed cell `[0, h]` and one of `[d h, (d+1) h]` (`h N = π`, `|d| < N`). -/
def AngleRange : Prop :=
  ∀ (h : ℝ) (d : ℤ) (N : ℕ), 0 < h → h * N = π → |d| < N →
    ∀ φ φ' : ℝ, 0 ≤ φ → φ ≤ h → d * h ≤ φ' → φ' ≤ (d + 1) * h →
      Real.cos ((|d| + 1) * h) ≤ Real.cos (φ' - φ) ∧
      Real.cos (φ' - φ) ≤ (if |d| ≤ 1 then 1 else Real.cos ((|d| - 1) * h))

/-! ## T3: Lemma 4 -/

/-- T3: `frange` encloses `r² + q² + 2 r q c` over `[ρ1, ρ2] × [κ1, κ2] × [c1, c2]` (each end enclosed). -/
def FrangeSound : Prop :=
  ∀ (r1 r2 q1 q2 cmin cmax : Iv) (ρ1 ρ2 κ1 κ2 c1 c2 : ℝ),
    ivMem ρ1 r1 → ivMem ρ2 r2 → ivMem κ1 q1 → ivMem κ2 q2 → ivMem c1 cmin → ivMem c2 cmax →
    0 ≤ ρ1 → 0 ≤ κ1 → -1 ≤ c1 → c2 ≤ 1 →
    ∀ r q c : ℝ, ρ1 ≤ r → r ≤ ρ2 → κ1 ≤ q → q ≤ κ2 → c1 ≤ c → c ≤ c2 →
      fx (frange r1 r2 q1 q2 cmin cmax).1 ≤ r ^ 2 + q ^ 2 + 2 * r * q * c ∧
      r ^ 2 + q ^ 2 + 2 * r * q * c ≤ fx (frange r1 r2 q1 q2 cmin cmax).2

/-! ## T4: distances -/

/-- T4: `distHi` bounds the distance from an interval point to an exact point; `epsCell` bounds the distance from
the centroid to the points of a sector of width `h` (with `ch ∋ cos(h/2)`); `vertexDistHi` bounds the distances from
the two vertices of the unit circles around `a`, `b` (`0 < |a - b| < 2`) to `l`, when the computed `|a - b|` has a
positive lower end (else `Iv.div` falls back to `[-1, 1]`). -/
def DistSound : Prop :=
  (∀ (px py : Iv) (qx qy : ℤ) (x y : ℝ), ivMem x px → ivMem y py →
      edist2 (x, y) (fx qx, fx qy) ≤ fx (distHi px py qx qy)) ∧
  (∀ (R : Ring) (ch : Iv) (r1 r2 a h : ℝ), ivMem r1 R.r1 → ivMem r2 R.r2 → ivMem (secRho r1 r2 0 h) R.rhoc →
      ivMem (Real.cos (h / 2)) ch → 0 ≤ r1 → r1 < r2 → 0 < h → h ≤ π / 2 → -π ≤ a → a + h ≤ π →
      ∀ z ∈ sector r1 r2 a (a + h), edist2 z (secCentroid r1 r2 a (a + h)) ≤ fx (epsCell R ch)) ∧
  (∀ ax ay bx by_ lx ly : ℤ, 0 < sqDist (fx ax, fx ay) (fx bx, fx by_) → sqDist (fx ax, fx ay) (fx bx, fx by_) < 4 →
      0 < (Iv.sqrt (Iv.add (Iv.sqr (Iv.pt (bx - ax))) (Iv.sqr (Iv.pt (by_ - ay))))).lo →
      edist2 (vertexPts (fx ax, fx ay) (fx bx, fx by_)).1 (fx lx, fx ly) ≤ fx (vertexDistHi ax ay bx by_ lx ly).1 ∧
      edist2 (vertexPts (fx ax, fx ay) (fx bx, fx by_)).2 (fx lx, fx ly) ≤ fx (vertexDistHi ax ay bx by_ lx ly).2)

/-! ## T5: `A_1`, `A_2` -/

/-- T5: `A_1(z) = A1c(|z|)` (two unit disks, Green's formula). -/
def A1Radial : Prop := GreenFormula → ∀ z : Pt, A1 z = A1c (enorm2 z)

/-- T5: `A_2(w, z) = |B(-w) ∪ B(0) ∪ B(z)| - π - A_1(w)`. -/
def A2Union : Prop := ∀ w z : Pt, A2 w z = unionArea ![-w, (0 : Pt), z] - π - A1 w

/-- T5: `A_2(w, z) ≤ A_1(z)`. -/
def A2LeA1 : Prop := ∀ w z : Pt, A2 w z ≤ A1 z

/-! ## T6: the integrated vertex lemma -/

/-- The centroid of a set of finite positive measure. -/
def cen (S : Set Pt) : Pt :=
  ((volume S).toReal⁻¹ * ∫ z in S, z.1, (volume S).toReal⁻¹ * ∫ z in S, z.2)

/-- `S1_ij ≥ E(|δ_i| + |δ_j|)` from `m0 ≥ E|δ_0|²`, `m2 ≥ E|δ_2|²` (`δ_1 = 0`; `δ_0`, `δ_2` independent). -/
def pairS1 (m0 m2 : ℝ) (i j : Fin 3) : ℝ :=
  if i = 0 ∧ j = 1 then √m0 else if i = 1 ∧ j = 2 then √m2 else √m0 + √m2

/-- `S2_ij ≥ E(|δ_i| + |δ_j|)²`. -/
def pairS2 (m0 m2 : ℝ) (i j : Fin 3) : ℝ :=
  if i = 0 ∧ j = 1 then m0 else if i = 1 ∧ j = 2 then m2 else m0 + m2 + 2 * √m0 * √m2

/-- The integrated bound of `(|δ_i| + |δ_j|) T_ij(|δ_j - δ_i|)` (paper eq. (3.3)), from `S1`, `S2`. -/
def pairRem (dlo dhi : ℝ) (first : Bool) (S1 S2 : ℝ) : ℝ :=
  (if first then S2 / √(4 - dhi ^ 2) else (2 * Real.arcsin (min dhi 2 / 2) - 2 * Real.arcsin (dlo / 2)) * S1) +
    min (S2 / dlo) (π * S1)

/-- T6: the vertex lemma along segments, integrated over `Z × Z'` for the configurations `(-w, 0, z)`, expansion
point `c` (`c_1 = 0`): with `|cen Z + c_0| ≤ e0`, `|cen Z' - c_2| ≤ e2`, second moments about the centroids at most
`M0`, `M2`, and `A(c) ≤ U0`,
`∫_{Z×Z'} A(-w, 0, z) ≤ (U0 + 2(e0 + e2) + Σ_{i<j, d⁻_ij<2} ν_ij pairRem_ij) |Z| |Z'|`
(the gradient term uses `|∇_{y_i} A(c)| ≤ 2`). -/
def PairMean : Prop :=
  VertexLemmaSeg →
  ∀ (Z Z' : Set Pt) (c : Fin 3 → Pt) (eps : Fin 3 → ℝ) (dlo dhi : Fin 3 → Fin 3 → ℝ)
    (first : Fin 3 → Fin 3 → Bool) (U0 e0 e2 M0 M2 : ℝ),
    MeasurableSet Z → MeasurableSet Z' → volume Z ≠ 0 → volume Z ≠ ⊤ → volume Z' ≠ 0 → volume Z' ≠ ⊤ →
    Bornology.IsBounded Z → Bornology.IsBounded Z' →
    c 1 = 0 →
    (∀ i j, i < j → 0 < dlo i j) →
    (∀ i j, i < j → first i j = true → dhi i j < 2) →
    (∀ w ∈ Z, ∀ z ∈ Z', ∀ i j, i < j → ∀ t ∈ Icc (0 : ℝ) 1,
        dlo i j ≤ edist2 (segPt (c i) (![-w, (0 : Pt), z] i) t) (segPt (c j) (![-w, (0 : Pt), z] j) t) ∧
        edist2 (segPt (c i) (![-w, (0 : Pt), z] i) t) (segPt (c j) (![-w, (0 : Pt), z] j) t) ≤ dhi i j) →
    (∀ w ∈ Z, ∀ z ∈ Z', ∀ i, enorm2 (![-w, (0 : Pt), z] i - c i) ≤ eps i) →
    unionArea c ≤ U0 →
    edist2 (cen Z) (-c 0) ≤ e0 → edist2 (cen Z') (c 2) ≤ e2 →
    (volume Z).toReal⁻¹ * ∫ w in Z, sqDist w (cen Z) ≤ M0 →
    (volume Z').toReal⁻¹ * ∫ z in Z', sqDist z (cen Z') ≤ M2 →
    ∫ p in Z ×ˢ Z', unionArea ![-p.1, (0 : Pt), p.2] ≤
      (U0 + 2 * (e0 + e2) + ∑ i : Fin 3, ∑ j : Fin 3,
          (if i < j ∧ dlo i j < 2 then
            (nuCountSeg c eps dlo dhi first i j : ℝ) *
              pairRem (dlo i j) (dhi i j) (first i j) (pairS1 (M0 + e0 ^ 2) (M2 + e2 ^ 2) i j)
                (pairS2 (M0 + e0 ^ 2) (M2 + e2 ^ 2) i j)
          else 0)) * (volume Z).toReal * (volume Z').toReal

/-! ## T7: rotations -/

/-- T7: rotating both sectors of a pair by `φ` (all angles in `[-π, π]`) keeps the integral of `A_2`. -/
def RotA2 : Prop :=
  ∀ (r1 r2 a b q1 q2 a' b' φ : ℝ), 0 ≤ r1 → 0 ≤ q1 →
    -π ≤ a → b ≤ π → -π ≤ a' → b' ≤ π → -π ≤ a + φ → b + φ ≤ π → -π ≤ a' + φ → b' + φ ≤ π →
    ∫ p in sector r1 r2 a b ×ˢ sector q1 q2 a' b', A2 p.1 p.2 =
      ∫ p in sector r1 r2 (a + φ) (b + φ) ×ˢ sector q1 q2 (a' + φ) (b' + φ), A2 p.1 p.2

/-! ## T8: centroid and second moment of a sector -/

/-- T8: `cen (sector r1 r2 a b) = secCentroid r1 r2 a b`, and the mean of `|w - cen|²` over the sector is
`(r1² + r2²)/2 - secRho²`. -/
def SectorCen : Prop :=
  ∀ r1 r2 a b : ℝ, SecOK r1 r2 a b →
    cen (sector r1 r2 a b) = secCentroid r1 r2 a b ∧
    (volume (sector r1 r2 a b)).toReal⁻¹ * ∫ w in sector r1 r2 a b, sqDist w (cen (sector r1 r2 a b)) =
      (r1 ^ 2 + r2 ^ 2) / 2 - secRho r1 r2 a b ^ 2

end BHH.W2
