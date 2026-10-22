/-
Interfaces between the proof modules of `W2/`, as named `Prop`s.  Each module proves its `Prop`; the assembly
uses them.  Definitions only.

* L (Laplace):  `LaplaceBound k`  sorted coordinates (paper Lemma 4.1), `ĝ ≤ g` (Lemma 4.2, proved in
  `W2/Graph.lean`), the window-2 area bound, the Laplace transform and Tonelli (Lemma 4.4).
* D (discretisation): `DiscBound g`  `Ψ_k(t) ≥ Ψ^d_k(t)` for table data satisfying `TableSound g`
  (Jensen on product cells, marginals, sure edges, the pass `passVal2_le_Lam` of `W2/PassSound.lean`).
* T (t-integral):  `TIntBound`  the extended-secant lower bound of `(1/2) ∫ t^{s-1} e^{-πt} Ψ^d_k(t) dt` from
  enclosures at the grid points (log-convexity of `Ψ^d`).
* the table soundness (interval arithmetic, Lemma 4, hulls, moments, vertex lemma) and the recursion soundness
  (exact integer recursion bounds `Ψ^d`) are proved against the computational definitions in `W2Cert`.
-/
import W2.Defs
import BHH.Interfaces
import W2Cert.TInt

open MeasureTheory Set Real
open scoped ENNReal

noncomputable section

namespace BHH.W2

/-! ## Module L -/

/-- Lemmas 4.1, 4.2 and 4.4: `C_k ≥ (1/2) ∫_0^∞ t^{k-3/2} e^{-π t} Ψ_k(t) dt`. -/
def LaplaceBound (k : ℕ) : Prop :=
  3 ≤ k →
    ENNReal.ofReal (1 / 2) *
      ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t ^ ((k : ℝ) - 3 / 2) * Real.exp (-(π * t))) * Psi (k - 1) t
      ≤ C k

/-! ## Module D -/

/-- What the computation must guarantee about the tables (paper Section 4.4). -/
structure TableSound (g : GridR) (D : DiscData) : Prop where
  /-- the weights are nonnegative and at most the cell areas -/
  w_nonneg : ∀ ir, 0 ≤ D.w ir
  w_le : ∀ ir it, ir < g.NR → it < g.NT → D.w ir ≤ (volume (g.cell ir it)).toReal
  /-- the first-step exponent bounds the mean of `A_1` over a cell -/
  ub : ∀ ir it, ir < g.NR → it < g.NT →
    ∫ z in g.cell ir it, A1 z ≤ D.ub ir * (volume (g.cell ir it)).toReal
  /-- the pair exponent bounds the mean of `A_2` over a pair of cells (`z_{j-1} ∈ Z`, `z_j ∈ Z'`) -/
  ab : ∀ ir ir2 it it2, ir < g.NR → ir2 < g.NR → it < g.NT → it2 < g.NT →
    ∫ p in g.cell ir it ×ˢ g.cell ir2 it2, A2 p.1 p.2 ≤
      D.ab ir ir2 ((it2 : ℤ) - it) * (volume (g.cell ir it)).toReal * (volume (g.cell ir2 it2)).toReal
  /-- a sure edge `{i+1, i-1}`: `|z_{j-1} + z_j| ≤ 1` on the whole cell pair -/
  sc : ∀ ir ir2 it it2, ir < g.NR → ir2 < g.NR → it < g.NT → it2 < g.NT →
    D.sc ir ir2 ((it2 : ℤ) - it) = true → ∀ w ∈ g.cell ir it, ∀ z ∈ g.cell ir2 it2, sqDist (w + z) 0 ≤ 1
  /-- a sure edge `{i+1, i}`: `|z| ≤ 1` on the whole cell -/
  nf : ∀ ir it, ir < g.NR → it < g.NT → D.nf ir = true → ∀ z ∈ g.cell ir it, sqDist z 0 ≤ 1

/-- Discretisation (paper Section 4.4, Jensen per product cell): `Ψ^d_k(t) ≤ Ψ_k(t)`. -/
def DiscBound (g : GridR) : Prop :=
  ∀ (hNR : 0 < g.NR) (hNT : 0 < g.NT) (D : DiscData), TableSound g D →
    ∀ (m : ℕ), 2 ≤ m → ∀ t : ℝ, 0 ≤ t → ENNReal.ofReal (Psid g hNR hNT D m t) ≤ Psi m t

/-! ## Module T -/

/-- A positive combination of decreasing exponentials `Σ_i c_i e^{-a_i t}` (`c_i ≥ 0`, `a_i ≥ 0`). -/
def IsExpSum (f : ℝ → ℝ) : Prop :=
  ∃ (n : ℕ) (c a : Fin n → ℝ), (∀ i, 0 ≤ c i) ∧ (∀ i, 0 ≤ a i) ∧ ∀ t, f t = ∑ i, c i * Real.exp (-(a i * t))

/-- Module T (paper Section 4.4, the t-integral): for every positive exponential sum `f` with enclosures
`L[j] ≤ log f(t_j) ≤ H[j]` at `t_j = j 2^-dtl` (`1 ≤ j ≤ ntv`, fixed point `2^-PR`) and lower bounds `logs[i]` of
`log(i 2^-(dtl + lsub))`, the value of `W2C.ckLo` (the extended-secant pieces, each integrated by `2^lsub`
sub-intervals, summed over `[0, ntv 2^-dtl]` and halved) is at most `(1/2) ∫_0^∞ t^{k-3/2} e^{-πt} f(t) dt`. -/
def TIntBound : Prop :=
  ∀ (k dtl ntv lsub : ℕ) (f : ℝ → ℝ) (L H logs : Array ℤ),
    3 ≤ k → 2 ≤ ntv → IsExpSum f →
    L.size = ntv + 1 → H.size = ntv + 1 → logs.size = ntv * 2 ^ lsub + 1 →
    (∀ j, 1 ≤ j → j ≤ ntv →
      0 < f ((j : ℝ) / 2 ^ dtl) ∧ fx L[j]! ≤ Real.log (f ((j : ℝ) / 2 ^ dtl)) ∧
      Real.log (f ((j : ℝ) / 2 ^ dtl)) ≤ fx H[j]!) →
    (∀ i, 1 ≤ i → i ≤ ntv * 2 ^ lsub → fx logs[i]! ≤ Real.log ((i : ℝ) / 2 ^ (dtl + lsub))) →
    ENNReal.ofReal (fx (W2C.ckLo k dtl ntv lsub L H logs)) ≤
      ENNReal.ofReal (1 / 2) *
        ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t ^ ((k : ℝ) - 3 / 2) * Real.exp (-(π * t))) * ENNReal.ofReal (f t)

end BHH.W2
