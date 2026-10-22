/-
Interfaces between the proof modules of the box part (k = 3, 4, 5), as named `Prop`s.  Each module proves its
`Prop`s; the others use them as hypotheses until the proofs land.  Definitions only.

Modules:
* A  `BHH/Ivl/*`      interval arithmetic, square roots, cos/sin, arcsin, φ powers         -> `CosSinSound`, lemmas
* B  `BHH/UnionSound` union-area enclosure (greenArea, greenGrad) from certified arcs      -> `UnionSoundProp`
* C  `BHH/Box/*`      measure theory on boxes: brackets, events, probabilities, moments     -> `BracketProp`, ...
* D  `BHH/LeafSound`  the leaf function is sound                                         -> `LeafSoundProp`
* E  `BHH/Tree`, `BHH/Domain`, `BHH/Graph`, `BHH/MainV2`: bisection tree, Lemma 2.2, g table, assembly
-/
import BHH.DefsV2
import BHHCert.Leaf

open MeasureTheory Set Real
open scoped ENNReal

noncomputable section

namespace BHH

open BHH.Cert

/-! ## Coordinates of the box part -/

/-- number of coordinates `m = 2k - 3` -/
def mDim (k : ℕ) : ℕ := 2 * k - 3

/-- coordinate `d` of `x` (0 outside the range) -/
def xget {m : ℕ} (x : Fin m → ℝ) (d : ℕ) : ℝ := if h : d < m then x ⟨d, h⟩ else 0

/-- The configuration of a point `x = (r_2, ξ_2, η_2, ..., ξ_{k-1}, η_{k-1})`: `y_0 = 0`, `y_1 = (x_0, 0)`,
`y_j = (x_{2j-3}, x_{2j-2})` (paper Section 2 with the indices shifted by one). -/
def xcfg (k : ℕ) (x : Fin (mDim k) → ℝ) : Fin k → Pt := fun i =>
  if i.val = 0 then (0, 0)
  else if i.val = 1 then (xget x 0, 0)
  else (xget x (2 * i.val - 3), xget x (2 * i.val - 2))

/-- The symmetry domain `D_k`: `r_2 ≥ 0`, `η_2 ≥ 0`, `ξ_2 ≤ ξ_3 ≤ ... ≤ ξ_{k-1}`. -/
def Dk (k : ℕ) : Set (Fin (mDim k) → ℝ) :=
  {x | 0 ≤ xget x 0 ∧ 0 ≤ xget x 2 ∧
    ∀ j : ℕ, 2 ≤ j → j + 1 < k → xget x (2 * j - 3) ≤ xget x (2 * (j + 1) - 3)}

/-- The root box `X_k` (half-open): `r_2 ∈ [0, k-2)`, `η_2 ∈ [0, k-2)`, the other coordinates in `[-(k-2), k-2)`. -/
def Xk (k : ℕ) : Set (Fin (mDim k) → ℝ) :=
  Set.pi univ fun d => Ico (if d.val = 0 ∨ d.val = 2 then 0 else -((k : ℝ) - 2)) ((k : ℝ) - 2)

/-- The integrand of the box part in `2g` units: `r_2 · 2g(G_1(y)) · A(y)^{-(k - 1/2)}`. -/
def F2 (k : ℕ) (x : Fin (mDim k) → ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (xget x 0 * (2 * dcG (unitGraph (xcfg k x))) * unionArea (xcfg k x) ^ (-((k : ℝ) - 1 / 2)))

/-- `κ_k = 2π Γ(k - 1/2) (k-2)! / k!` -/
def kappa (k : ℕ) : ℝ := 2 * π * Real.Gamma ((k : ℝ) - 1 / 2) * ((k - 2).factorial : ℝ) / (k.factorial : ℝ)

/-- Lemma 2.2 (the direction used): `C_k ≥ (κ_k / 2) ∫_{D_k ∩ X_k} r_2 2g φ(A)` (module E). -/
def DomainReductionProp (k : ℕ) : Prop :=
  ENNReal.ofReal (kappa k / 2) * ∫⁻ x in Dk k ∩ Xk k, F2 k x ≤ C k

/-! ## Boxes given by fixed-point corners -/

/-- fixed-point integer to real: `n / 2^PR` -/
def fx (n : ℤ) : ℝ := (n : ℝ) / (2 : ℝ) ^ PR

/-- the half-open box with fixed-point corners `lo`, `hi` -/
def boxOf {m : ℕ} (lo hi : List ℤ) : Set (Fin m → ℝ) :=
  Set.pi univ fun d => Ico (fx (lo.getD d.val 0)) (fx (hi.getD d.val 0))

/-- What the leaf function may assume about a box: the right number of corners, positive widths, exact centres
(`lo + hi` even), and the box inside the root box. -/
def ValidBox (k : ℕ) (lo hi : List ℤ) : Prop :=
  lo.length = mDim k ∧ hi.length = mDim k ∧
  (∀ d < mDim k, lo.getD d 0 < hi.getD d 0 ∧ Even (lo.getD d 0 + hi.getD d 0)) ∧
  (boxOf lo hi : Set (Fin (mDim k) → ℝ)) ⊆ Xk k

/-- Leaf soundness (module D): the integer value `L lo hi` at scale `2^-OS` is at most the integral of the
integrand over the box intersected with `D_k`. -/
def LeafSoundProp (k : ℕ) (L : List ℤ → List ℤ → ℤ) : Prop :=
  ∀ lo hi : List ℤ, ValidBox k lo hi →
    ENNReal.ofReal ((L lo hi : ℝ) / (2 : ℝ) ^ OS) ≤ ∫⁻ x in boxOf lo hi ∩ Dk k, F2 k x

/-! ## Computation-side specifications -/

/-- interval membership: `a.lo ≤ x · 2^PR ≤ a.hi` -/
def ivMem (x : ℝ) (a : Iv) : Prop := (a.lo : ℝ) ≤ x * (2 : ℝ) ^ PR ∧ x * (2 : ℝ) ^ PR ≤ (a.hi : ℝ)

/-- a sound cos/sin enclosure function (module A proves it for `cosSin`; the table version too) -/
def CosSinSound (cs : ℤ → Iv × Iv) : Prop :=
  ∀ t : ℤ, t.natAbs ≤ 7 * ONE.toNat → ivMem (Real.cos (fx t)) (cs t).1 ∧ ivMem (Real.sin (fx t)) (cs t).2

/-- the configuration of `k` fixed-point points given as a list (`(0, 0)` beyond the list) -/
def ptsCfg (k : ℕ) (pts : List (ℤ × ℤ)) : Fin k → Pt :=
  fun i => (fx (pts.getD i.val (0, 0)).1, fx (pts.getD i.val (0, 0)).2)

/-- Union-area enclosure (module B), unit radius: if the computation succeeds, it encloses the union area (via Green's
formula) and the gradient formula at the given points. -/
def UnionSoundProp : Prop :=
  GreenFormula → ∀ (cs : ℤ → Iv × Iv), CosSinSound cs → ∀ (cand : CandFn) (k : ℕ) (pts : List (ℤ × ℤ)) (u : UnionRes),
    pts.length = k → BHH.Cert.unionArea cs pts ONE cand = some u →
      ivMem (BHH.unionArea (ptsCfg k pts)) u.A ∧
      ∀ i : Fin k,
        ivMem (greenGrad (ptsCfg k pts) i).1 (u.gx.getD i.val default) ∧
        ivMem (greenGrad (ptsCfg k pts) i).2 (u.gy.getD i.val default)

/-- Union-area enclosure (module B), radius `R > 0` (for Prop 3.8): the area of the union of the disks `B(c_i, R)`. -/
def UnionSoundRProp : Prop :=
  GreenFormula → ∀ (cs : ℤ → Iv × Iv), CosSinSound cs → ∀ (cand : CandFn) (k : ℕ) (pts : List (ℤ × ℤ)) (R : ℤ)
    (u : UnionRes), pts.length = k → 0 < R → BHH.Cert.unionArea cs pts R cand = some u →
      ivMem (volume (⋃ i, disk (ptsCfg k pts i) (fx R))).toReal u.A

/-! ## The g table -/

/-- the graph on `Fin k` with the edges of the bitmask `e` (bit `p` = the `p`-th pair of `pairList k`) -/
def graphOf (k : ℕ) (e : ℕ) : SimpleGraph (Fin k) where
  Adj i j := i ≠ j ∧ ∃ p < (pairList k).length,
    ((pairList k).getD p (0, 0) = (i.val, j.val) ∨ (pairList k).getD p (0, 0) = (j.val, i.val)) ∧ e.testBit p
  symm := ⟨fun i j h => ⟨h.1.symm, by
    obtain ⟨p, hp, h1, h2⟩ := h.2; exact ⟨p, hp, h1.symm, h2⟩⟩⟩
  loopless := ⟨fun i h => h.1 rfl⟩

/-- `e` completes the edge state `idx` (base 3, digit 0 absent, 1 present, 2 undetermined) -/
def Completes (k : ℕ) (idx e : ℕ) : Prop :=
  e < 2 ^ (pairList k).length ∧
  ∀ p < (pairList k).length, (idx / 3 ^ p % 3 = 1 → e.testBit p) ∧ (idx / 3 ^ p % 3 = 0 → ¬ e.testBit p)

/-- a sound g table (module E proves it for the tables used): `gmin idx ≤ 2 g(G)` for every completion `G`. -/
def GTabSound (k : ℕ) (gt : GTab) : Prop :=
  ∀ idx e : ℕ, idx < 3 ^ (pairList k).length → Completes k idx e →
    (gt.gmin idx : ℝ) ≤ 2 * dcG (graphOf k e)

/-! ## Measure theory on boxes (module C) -/

/-- `φ(t) = t^{-s}` -/
def phiS (s t : ℝ) : ℝ := t ^ (-s)

/-- the closed box with real corners -/
def rbox {m : ℕ} (lo hi : Fin m → ℝ) : Set (Fin m → ℝ) := Set.pi univ fun d => Icc (lo d) (hi d)

/-- Prop 3.4 and its second bracket, geometry-free: on a box with `0 ≤ lo_0` (coordinate 0 is `r_2`), if
`Z(x) = a + ⟨b, x - c⟩ + ρ(x)` with `ρ ≥ 0`, `E ρ ≤ R̄`, `E ρ² ≤ S̄²` (uniform measure), `τ > 0`, and `f ≥ r_2 φ(Z)`
on the box, then `∫ f ≥ v · max(V_B, V_A)`. -/
def BracketProp : Prop :=
  ∀ (m : ℕ) (lo hi : Fin (m + 1) → ℝ) (s a Rbar Sbar : ℝ) (b : Fin (m + 1) → ℝ)
    (ρ : (Fin (m + 1) → ℝ) → ℝ) (f : (Fin (m + 1) → ℝ) → ℝ≥0∞),
    (∀ d, lo d < hi d) → 0 ≤ lo 0 → 0 < s → 0 ≤ Rbar → 0 ≤ Sbar →
    Measurable ρ → (∃ M, ∀ x ∈ rbox lo hi, 0 ≤ ρ x ∧ ρ x ≤ M) →
    (∫ x in rbox lo hi, ρ x) ≤ Rbar * (volume (rbox lo hi)).toReal →
    (∫ x in rbox lo hi, ρ x ^ 2) ≤ Sbar ^ 2 * (volume (rbox lo hi)).toReal →
    let v := ∏ d, (hi d - lo d)
    let c : Fin (m + 1) → ℝ := fun d => (lo d + hi d) / 2
    let h0 := hi 0 - lo 0
    let τ := a - ∑ d, |b d| * (hi d - lo d) / 2
    let Sb := √(∑ d, (b d) ^ 2 * (hi d - lo d) ^ 2 / 12)
    0 < τ →
    (∀ x ∈ rbox lo hi, ENNReal.ofReal (x 0 * phiS s (a + ∑ d, b d * (x d - c d) + ρ x)) ≤ f x) →
    let rbar := c 0
    let d1 := fun t : ℝ => -s * t ^ (-s - 1)            -- φ'
    let d2 := fun t : ℝ => s * (s + 1) * t ^ (-s - 2)   -- φ''
    let VB := rbar * phiS s (a + Rbar) + d1 a * (b 0 * h0 ^ 2 / 12) - |d1 a| * (h0 / 2) * Rbar
      - h0 / 4 * d2 τ * (Sb + Sbar) ^ 2
    let VA := rbar * phiS s (a + Rbar) + d1 (a + Rbar) * (b 0 * h0 ^ 2 / 12) - |d1 (a + Rbar)| * (h0 / 2) * Rbar
      - h0 / 4 * d2 τ * (Sb + √(Sbar ^ 2 + Rbar ^ 2)) ^ 2
    ENNReal.ofReal (v * max VB VA) ≤ ∫⁻ x in rbox lo hi, f x

end BHH
