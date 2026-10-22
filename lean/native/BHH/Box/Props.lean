/-
Module C (box lemmas): statements, as named `Prop`s (definitions only).
`BracketProp` itself is in `BHH/Interfaces.lean`.

* `EventBoundProp`      Lemma 3.5 (generic measure theory)
* `PartitionBoundProp`  the integration step of Prop 3.6 (`g ≥ gmin + Σ_σ (g_σ - gmin) 1_{F_σ}`)
* `CdfIvProp`           `cdfIv` encloses the distribution function `cdfR` of a difference of uniforms
* `ProbStripsProp`      `probStrips` gives lower bounds for the volumes of the edge events (8-strip staircase)
* `EdgeIndepProp`       edge events of vertex-disjoint pairs are independent on a box (Frechet is a lemma)
* `StraddleProp`        Prop 3.7: `boxOf ∩ D_k` for one straddling pair, and its volume via `cdfIv`
* `EnlargedDisksProp`, `UnionAreaGePiProp`  Prop 3.8 (geometric part) and `A(y) ≥ π`
* `PointDispProp`, `RemMaxProp`, `RemMomentsProp`  Lemma 3.3 and the bounds for `ϱ = vertexRemSeg` on a box
-/
import BHH.Interfaces

open MeasureTheory Set Real
open scoped ENNReal

noncomputable section

namespace BHH

open BHH.Cert

/-! ## Lemma 3.5 and the integration step of Prop 3.6 -/

/-- Lemma 3.5 (generic): on a measurable set `Q` of finite volume `v`, if `fmin ≤ f ≤ fmax` on `Q`,
`∫⁻_Q f ≥ v V*` and `F ⊆ Q` is measurable with `vol F ≥ q v`, then `∫⁻_F f ≥ v max(q fmin, V* - (1 - q) fmax)`. -/
def EventBoundProp : Prop :=
  ∀ (m : ℕ) (Q F : Set (Fin m → ℝ)) (f : (Fin m → ℝ) → ℝ≥0∞) (q fmin fmax Vs : ℝ),
    MeasurableSet Q → MeasurableSet F → F ⊆ Q → volume Q ≠ ⊤ →
    0 ≤ q → 0 ≤ fmin → 0 ≤ fmax →
    ENNReal.ofReal (q * (volume Q).toReal) ≤ volume F →
    (∀ x ∈ Q, ENNReal.ofReal fmin ≤ f x) → (∀ x ∈ Q, f x ≤ ENNReal.ofReal fmax) →
    ENNReal.ofReal ((volume Q).toReal * Vs) ≤ ∫⁻ x in Q, f x →
    ENNReal.ofReal ((volume Q).toReal * max (q * fmin) (Vs - (1 - q) * fmax)) ≤ ∫⁻ x in F, f x

/-- The integration step of Prop 3.6: if `G ≥ g0 + Σ_σ w_σ 1_{F_σ}` on `Q` (`g0, w_σ ≥ 0`, measurable `F_σ ⊆ Q`), then
`∫⁻_Q G f ≥ g0 ∫⁻_Q f + Σ_σ w_σ ∫⁻_{F_σ} f`. -/
def PartitionBoundProp : Prop :=
  ∀ (m : ℕ) (ι : Type) (S : Finset ι) (Q : Set (Fin m → ℝ)) (F : ι → Set (Fin m → ℝ))
    (f : (Fin m → ℝ) → ℝ≥0∞) (G : (Fin m → ℝ) → ℝ) (g0 : ℝ) (w : ι → ℝ),
    MeasurableSet Q → (∀ σ ∈ S, MeasurableSet (F σ)) → (∀ σ ∈ S, F σ ⊆ Q) → 0 ≤ g0 → (∀ σ ∈ S, 0 ≤ w σ) →
    (∀ x ∈ Q, g0 + ∑ σ ∈ S, w σ * (F σ).indicator (fun _ => (1 : ℝ)) x ≤ G x) →
    ENNReal.ofReal g0 * (∫⁻ x in Q, f x) + ∑ σ ∈ S, ENNReal.ofReal (w σ) * ∫⁻ x in F σ, f x ≤
      ∫⁻ x in Q, ENNReal.ofReal (G x) * f x

/-! ## Probabilities of edge events -/

/-- `max t 0` -/
def ramp (t : ℝ) : ℝ := max t 0

/-- The distribution function `P(X - Y ≤ z)` of the difference of independent uniform variables `X` on `[a, b]` and `Y` on
`[c, d]` (a point mass when the interval is a point; `a ≤ b`, `c ≤ d`). -/
def cdfR (a b c d z : ℝ) : ℝ :=
  if a = b ∧ c = d then (if a - c ≤ z then 1 else 0)
  else if a = b then min (max ((z + d - a) / (d - c)) 0) 1
  else if c = d then min (max ((z + c - a) / (b - a)) 0) 1
  else (ramp (z + d - a) ^ 2 - ramp (z + d - b) ^ 2 - ramp (z + c - a) ^ 2 + ramp (z + c - b) ^ 2) /
    (2 * (b - a) * (d - c))

/-- `cdfIv` encloses `cdfR` (fixed-point inputs). -/
def CdfIvProp : Prop :=
  ∀ a b c d z : ℤ, a ≤ b → c ≤ d → ivMem (cdfR (fx a) (fx b) (fx c) (fx d) (fx z)) (cdfIv a b c d z)

/-- The edge events on a box (paper Sec. 3.4): `probStrips` gives lower bounds for the probabilities, under the uniform
measure on the box, that the edge `ij` is present (`|y_i - y_j| ≤ 1`) and absent. -/
def ProbStripsProp : Prop :=
  ∀ (k : ℕ) (lo hi : List ℤ), ValidBox k lo hi → ∀ i j : Fin k, i < j →
    ENNReal.ofReal (fx (probStrips ((ptBoxes k lo hi).getD i.val default)
        ((ptBoxes k lo hi).getD j.val default)).1 * (volume (boxOf lo hi : Set (Fin (mDim k) → ℝ))).toReal) ≤
      volume {x ∈ (boxOf lo hi : Set (Fin (mDim k) → ℝ)) | sqDist (xcfg k x i) (xcfg k x j) ≤ 1} ∧
    ENNReal.ofReal (fx (probStrips ((ptBoxes k lo hi).getD i.val default)
        ((ptBoxes k lo hi).getD j.val default)).2 * (volume (boxOf lo hi : Set (Fin (mDim k) → ℝ))).toReal) ≤
      volume {x ∈ (boxOf lo hi : Set (Fin (mDim k) → ℝ)) | 1 < sqDist (xcfg k x i) (xcfg k x j)}

/-- Edge events of two vertex-disjoint pairs are independent under the uniform measure on a box
(`vol(F₁ ∩ F₂) vol(Q) = vol(F₁) vol(F₂)`). -/
def EdgeIndepProp : Prop :=
  ∀ (k : ℕ) (lo hi : List ℤ), ValidBox k lo hi → ∀ i₁ j₁ i₂ j₂ : Fin k,
    i₁ ≠ i₂ → i₁ ≠ j₂ → j₁ ≠ i₂ → j₁ ≠ j₂ → ∀ S₁ S₂ : Set ℝ, MeasurableSet S₁ → MeasurableSet S₂ →
    volume {x ∈ (boxOf lo hi : Set (Fin (mDim k) → ℝ)) |
        sqDist (xcfg k x i₁) (xcfg k x j₁) ∈ S₁ ∧ sqDist (xcfg k x i₂) (xcfg k x j₂) ∈ S₂} *
      volume (boxOf lo hi : Set (Fin (mDim k) → ℝ)) =
    volume {x ∈ (boxOf lo hi : Set (Fin (mDim k) → ℝ)) | sqDist (xcfg k x i₁) (xcfg k x j₁) ∈ S₁} *
      volume {x ∈ (boxOf lo hi : Set (Fin (mDim k) → ℝ)) | sqDist (xcfg k x i₂) (xcfg k x j₂) ∈ S₂}

/-- Prop 3.7, set and volume part: if `r_2 ≥ 0` and `η_2 ≥ 0` on the box and every ordered pair other than `(j, j+1)`
is in order on the box, then `boxOf ∩ D_k` is the event `ξ_j ≤ ξ_{j+1}`, whose volume is at least
`cdfIv(ξ_j-range, ξ_{j+1}-range, 0).lo · vol`. -/
def StraddleProp : Prop :=
  ∀ (k : ℕ) (lo hi : List ℤ) (j : ℕ), ValidBox k lo hi → 2 ≤ j → j + 1 < k →
    0 ≤ lo.getD 0 0 → (2 < k → 0 ≤ lo.getD 2 0) →
    (∀ j', 2 ≤ j' → j' + 1 < k → j' ≠ j → hi.getD (2 * j' - 3) 0 ≤ lo.getD (2 * (j' + 1) - 3) 0) →
    (boxOf lo hi : Set (Fin (mDim k) → ℝ)) ∩ Dk k =
        {x ∈ (boxOf lo hi : Set (Fin (mDim k) → ℝ)) | xget x (2 * j - 3) ≤ xget x (2 * (j + 1) - 3)} ∧
    ENNReal.ofReal (fx (cdfIv (lo.getD (2 * j - 3) 0) (hi.getD (2 * j - 3) 0)
        (lo.getD (2 * (j + 1) - 3) 0) (hi.getD (2 * (j + 1) - 3) 0) 0).lo *
        (volume (boxOf lo hi : Set (Fin (mDim k) → ℝ))).toReal) ≤
      volume {x ∈ (boxOf lo hi : Set (Fin (mDim k) → ℝ)) | xget x (2 * j - 3) ≤ xget x (2 * (j + 1) - 3)}

/-! ## Prop 3.8 (geometric part) -/

/-- Prop 3.8, geometric part: if `|y_i - c_i| ≤ ε` for all `i`, then `A(y)` is at most the area of the union of the
disks `B(c_i, 1 + ε)` (and that area is finite). -/
def EnlargedDisksProp : Prop :=
  ∀ (k : ℕ) (y c : Fin k → Pt) (ε : ℝ), (∀ i, edist2 (y i) (c i) ≤ ε) →
    volume (⋃ i, disk (c i) (1 + ε)) ≠ ⊤ ∧ unionArea y ≤ (volume (⋃ i, disk (c i) (1 + ε))).toReal

/-- The union of at least one unit disk has area at least `π`. -/
def UnionAreaGePiProp : Prop :=
  ∀ (k : ℕ) (y : Fin k → Pt), 0 < k → π ≤ unionArea y

/-! ## Lemma 3.3 and the vertex remainder on a box -/

/-- half-sides `(σ_j, σ'_j)` of the rectangle `R_j` of the point `j` on the box with real corners `lo`, `hi` -/
def halfSides (k : ℕ) (lo hi : Fin (mDim k) → ℝ) (j : Fin k) : ℝ × ℝ :=
  if j.val = 0 then (0, 0)
  else if j.val = 1 then ((xget hi 0 - xget lo 0) / 2, 0)
  else ((xget hi (2 * j.val - 3) - xget lo (2 * j.val - 3)) / 2,
        (xget hi (2 * j.val - 2) - xget lo (2 * j.val - 2)) / 2)

/-- `E|δ_j|² = (σ² + σ'²)/3` for `δ_j` uniform on a rectangle with half-sides `σ, σ'` -/
def m2pt (σ : ℝ × ℝ) : ℝ := (σ.1 ^ 2 + σ.2 ^ 2) / 3

/-- `E|δ_j|⁴ = σ⁴/5 + 2σ²σ'²/9 + σ'⁴/5` -/
def m4pt (σ : ℝ × ℝ) : ℝ := σ.1 ^ 4 / 5 + 2 * σ.1 ^ 2 * σ.2 ^ 2 / 9 + σ.2 ^ 4 / 5

/-- `λ` of `T(w) = λ w + μ + min(w/d⁻, π)` (as in `Tseg`) -/
def lamT (dhi : ℝ) (first : Bool) : ℝ := if first then 1 / √(4 - dhi ^ 2) else 0

/-- `μ` of `T(w) = λ w + μ + min(w/d⁻, π)` (as in `Tseg`) -/
def muT (dlo dhi : ℝ) (first : Bool) : ℝ :=
  if first then 0 else 2 * Real.arcsin (min dhi 2 / 2) - 2 * Real.arcsin (dlo / 2)

/-- Half-diagonals: on the closed box, `|y_j - c_j| ≤ √(σ_j² + σ'_j²)`. -/
def PointDispProp : Prop :=
  ∀ (k : ℕ) (lo hi : Fin (mDim k) → ℝ), (∀ d, lo d ≤ hi d) → ∀ x ∈ rbox lo hi, ∀ j : Fin k,
    enorm2 (xcfg k x j - xcfg k (fun d => (lo d + hi d) / 2) j) ≤
      √((halfSides k lo hi j).1 ^ 2 + (halfSides k lo hi j).2 ^ 2)

/-- `ϱ ≤ R_max` (paper (3.4)): if `|y_i - c_i| ≤ ε_i` for all `i` and `0 < d⁻ ≤ d⁺` for the pairs in the sum, then
`ϱ(y - c) ≤ Σ_{i<j, d⁻<2} ν_ij (ε_i + ε_j) T_ij(ε_i + ε_j)`. -/
def RemMaxProp : Prop :=
  ∀ (k : ℕ) (c y : Fin k → Pt) (eps : Fin k → ℝ) (dlo dhi : Fin k → Fin k → ℝ) (first : Fin k → Fin k → Bool),
    (∀ i j, i < j → dlo i j < 2 → 0 < dlo i j ∧ dlo i j ≤ dhi i j) →
    (∀ i, enorm2 (y i - c i) ≤ eps i) →
    vertexRemSeg c y eps dlo dhi first ≤
      ∑ i, ∑ j, if i < j ∧ dlo i j < 2 then
        (nuCountSeg c eps dlo dhi first i j : ℝ) * (eps i + eps j) *
          Tseg (dlo i j) (dhi i j) (first i j) (eps i + eps j)
      else 0

/-- Lemma 3.3 for `ϱ = vertexRemSeg` on a box with real corners (uniform measure): measurability, `ϱ ≥ 0`, and the
bounds `E ϱ ≤ Σ ν (λ Eχ² + μ Eχ + min(Eχ²/d⁻, π Eχ))`,
`(E ϱ²)^{1/2} ≤ Σ ν (3λ² Eχ⁴ + 3μ² Eχ² + 3 min(Eχ⁴/(d⁻)², π² Eχ²))^{1/2}`, with `χ = |δ_i| + |δ_j|` and
`Eχ ≤ m₁(i) + m₁(j)`, `Eχ² ≤ m₂(i) + m₂(j) + 2 m₁(i) m₁(j)`, `Eχ⁴ ≤ 8 (m₄(i) + m₄(j))`, `m₁ = √m₂`. -/
def RemMomentsProp : Prop :=
  ∀ (k : ℕ) (lo hi : Fin (mDim k) → ℝ) (eps : Fin k → ℝ) (dlo dhi : Fin k → Fin k → ℝ)
    (first : Fin k → Fin k → Bool),
    (∀ d, lo d < hi d) →
    (∀ i j, i < j → dlo i j < 2 → 0 < dlo i j ∧ dlo i j ≤ dhi i j) →
    let c := xcfg k (fun d => (lo d + hi d) / 2)
    let ρ : (Fin (mDim k) → ℝ) → ℝ := fun x => vertexRemSeg c (xcfg k x) eps dlo dhi first
    let m2 := fun j => m2pt (halfSides k lo hi j)
    let m4 := fun j => m4pt (halfSides k lo hi j)
    let E1 := fun i j => √(m2 i) + √(m2 j)
    let E2 := fun i j => m2 i + m2 j + 2 * √(m2 i) * √(m2 j)
    let E4 := fun i j => 8 * (m4 i + m4 j)
    let ν := fun i j => (nuCountSeg c eps dlo dhi first i j : ℝ)
    let L := fun i j => lamT (dhi i j) (first i j)
    let U := fun i j => muT (dlo i j) (dhi i j) (first i j)
    Measurable ρ ∧ (∀ x, 0 ≤ ρ x) ∧
    (∫ x in rbox lo hi, ρ x) ≤
      (∑ i, ∑ j, if i < j ∧ dlo i j < 2 then
        ν i j * (L i j * E2 i j + U i j * E1 i j + min (E2 i j / dlo i j) (π * E1 i j)) else 0) *
        (volume (rbox lo hi)).toReal ∧
    (∫ x in rbox lo hi, ρ x ^ 2) ≤
      (∑ i, ∑ j, if i < j ∧ dlo i j < 2 then
        ν i j * √(3 * L i j ^ 2 * E4 i j + 3 * U i j ^ 2 * E2 i j +
          3 * min (E4 i j / dlo i j ^ 2) (π ^ 2 * E2 i j)) else 0) ^ 2 *
        (volume (rbox lo hi)).toReal

end BHH
