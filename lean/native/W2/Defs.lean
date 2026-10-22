/-
Definitions of the window-2 reduction (version 2 of the paper, Section 4), used by the proof modules of `W2/`.
Definitions only; nothing is assumed.

Points `y_0, ..., y_{k-1}` are given by the increments `z_j = y_{j+1} - y_j` (`j < k - 1`), `y_0 = 0`.
-/
import BHH.Defs
import W2.Graph
import W2.PassSound
import W2.A1

open MeasureTheory Set Real
open scoped ENNReal

noncomputable section

namespace BHH.W2

/-! ## Increments, areas, the integrand -/

/-- The open right half-plane `H = {z : z.1 > 0}`. -/
def Hp : Set Pt := {z | 0 < z.1}

/-- The configuration of the partial sums: `y_i = Σ_{j < i} z_j`, `y_0 = 0`. -/
def psum {m : ℕ} (z : Fin m → Pt) : Fin (m + 1) → Pt :=
  fun i => ∑ j : Fin m, if j.val < i.val then z j else 0

/-- The `j`-th increment, `0` outside the range. -/
def zget {m : ℕ} (z : Fin m → Pt) (j : ℕ) : Pt := if h : j < m then z ⟨j, h⟩ else 0

/-- `A_1(z) = |B(z,1) \ B(0,1)|`. -/
def A1 (z : Pt) : ℝ := (volume (disk z 1 \ disk 0 1)).toReal

/-- `A_2(w, z) = |B(z,1) \ (B(0,1) ∪ B(-w,1))|`. -/
def A2 (w z : Pt) : ℝ := (volume (disk z 1 \ (disk 0 1 ∪ disk (-w) 1))).toReal

/-- The window-2 area bound minus `π`: `A_1(z_0) + Σ_{j ≥ 1} A_2(z_{j-1}, z_j)`. -/
def Xsum {m : ℕ} (z : Fin m → Pt) : ℝ :=
  A1 (zget z 0) + ∑ j ∈ Finset.Ico 1 m, A2 (zget z (j - 1)) (zget z j)

/-- `ĝ(z) = Λ(H(z))`: the value of the window graph of `G_1(y(z))`. -/
def ghat {m : ℕ} (z : Fin m → Pt) : ℝ := Lam (windowGraph (unitGraph (psum z)))

/-- `Ψ_k(t)` with `m = k - 1` increments: `∫_{H^m} ĝ(z) e^{-t X(z)} dz` (in `[0, ∞]`). -/
def Psi (m : ℕ) (t : ℝ) : ℝ≥0∞ :=
  ∫⁻ z : Fin m → Pt, Set.indicator {z | ∀ i, z i ∈ Hp}
    (fun z => ENNReal.ofReal (ghat z * Real.exp (-(t * Xsum z)))) z

/-! ## The polar grid -/

/-- Grid parameters: `N1` rings on `[0, 1]`, `N2` on `[1, 2]`, `NT` angular cells on `(-π/2, π/2)`. -/
structure GridR where
  N1 : ℕ
  N2 : ℕ
  NT : ℕ

namespace GridR

def NR (g : GridR) : ℕ := g.N1 + g.N2

/-- the radius `r_j` -/
def rad (g : GridR) (j : ℕ) : ℝ := if j ≤ g.N1 then (j : ℝ) / g.N1 else 1 + ((j - g.N1 : ℕ) : ℝ) / g.N2

/-- the angle `θ_i = -π/2 + i π / NT` -/
def ang (g : GridR) (i : ℕ) : ℝ := -(π / 2) + i * π / g.NT

/-- the open polar cell `{ρ u(φ) : r_ir < ρ < r_{ir+1}, θ_it < φ < θ_{it+1}}` -/
def cell (g : GridR) (ir it : ℕ) : Set Pt :=
  polarCoord.symm '' (Ioo (g.rad ir) (g.rad (ir + 1)) ×ˢ Ioo (g.ang it) (g.ang (it + 1)))

end GridR

/-! ## Discrete data (tables) and the discrete bound `Ψ^d` -/

/-- Table data, as real numbers: cell weights `w` (per ring), first-step exponents `ub` (per ring), pair
exponents `ab (ir, ir', d)`, the sure class of the edge `{i+1, i-1}` (`sc`) and of `{i+1, i}` (`nf`, per ring). -/
structure DiscData where
  w : ℕ → ℝ
  ub : ℕ → ℝ
  ab : ℕ → ℕ → ℤ → ℝ
  sc : ℕ → ℕ → ℤ → Bool
  nf : ℕ → Bool

/-- A sequence of cells `c_0, ..., c_{m-1}` (ring, angular index). -/
abbrev CellSeq (g : GridR) (m : ℕ) := Fin m → Fin g.NR × Fin g.NT

/-- the angular offset between two cells -/
def doff {g : GridR} (c c' : Fin g.NR × Fin g.NT) : ℤ := (c'.2.val : ℤ) - c.2.val

/-- `j`-th cell of a sequence (cell `(0,0)` outside the range; requires `NR, NT > 0`). -/
def cget {g : GridR} {m : ℕ} (hNR : 0 < g.NR) (hNT : 0 < g.NT) (c : CellSeq g m) (j : ℕ) :
    Fin g.NR × Fin g.NT := if h : j < m then c ⟨j, h⟩ else (⟨0, hNR⟩, ⟨0, hNT⟩)

/-- The sure-edge indicators of a cell sequence: `a1 i` for the edge `{i, i-1}` (`|z_{i-1}| ≤ 1` sure),
`a2 i` for `{i, i-2}` (`|z_{i-2} + z_{i-1}| ≤ 1` sure). -/
def edgeA1 {g : GridR} {m : ℕ} (hNR : 0 < g.NR) (hNT : 0 < g.NT) (D : DiscData) (c : CellSeq g m) (i : ℕ) :
    Bool := if 1 ≤ i then D.nf (cget hNR hNT c (i - 1)).1.val else false

def edgeA2 {g : GridR} {m : ℕ} (hNR : 0 < g.NR) (hNT : 0 < g.NT) (D : DiscData) (c : CellSeq g m) (i : ℕ) :
    Bool :=
  if 2 ≤ i then
    let p := cget hNR hNT c (i - 2)
    let q := cget hNR hNT c (i - 1)
    D.sc p.1.val q.1.val (doff p q)
  else false

/-- The exponent bound of a cell sequence: `ub(c_0) + Σ_{j ≥ 1} ab(c_{j-1}, c_j)`. -/
def expoSeq {g : GridR} {m : ℕ} (hNR : 0 < g.NR) (hNT : 0 < g.NT) (D : DiscData) (c : CellSeq g m) : ℝ :=
  D.ub (cget hNR hNT c 0).1.val + ∑ j ∈ Finset.Ico 1 m,
    D.ab (cget hNR hNT c (j - 1)).1.val (cget hNR hNT c j).1.val (doff (cget hNR hNT c (j - 1)) (cget hNR hNT c j))

/-- `Ψ^d_k(t)` (`m = k - 1`): `Σ_c (pass value) Π_j w(c_j) e^{-t (exponent bound)}`. -/
def Psid (g : GridR) (hNR : 0 < g.NR) (hNT : 0 < g.NT) (D : DiscData) (m : ℕ) (t : ℝ) : ℝ :=
  ∑ c : CellSeq g m, ((passVal2 (edgeA1 hNR hNT D c) (edgeA2 hNR hNT D c) (m + 1) : ℝ) / 2) *
    (∏ j, D.w (c j).1.val) * Real.exp (-(t * expoSeq hNR hNT D c))

end BHH.W2
