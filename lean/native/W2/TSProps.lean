/-
The table soundness of a production run from the entry bound (per table entry, on the canonical cells) and the
per-ring and angle facts of `W2/TabProps.lean`, as a named `Prop` for a separate proof module.  Definitions only.

`TableSound` (`W2/Interfaces.lean`) is about the grid cells `g.cell ir it` (sectors at angles
`(θ_it, θ_it + h)`, `θ_i = -π/2 + i h`, `h = π/NT`) and the run data `discOf g rings tab dtl` (`W2/Unroll.lean`),
whose table entries are `tab[tidx g ir ir2 d]! = prepE dtl (entryF g.prune rings (mkAData g) (mkDTab g)[di]! ir ir2)`
with `di = d + NT - 1` (`W2/RunData.lean`, `tab_getElem`).  The entry bound is about the canonical pair (z-cell at
angles `(0, h)`, z'-cell at `(d h, (d + 1) h)`); rotating by `-θ_it` (T7) maps the cells `(ir, it)`, `(ir2, it2)`
onto it with `d = it2 - it`.
-/
import W2.TabProps
import W2.RunData
import W2.EntryDefs
import W2.Interfaces

open MeasureTheory Set Real
open scoped ENNReal

noncomputable section

namespace BHH.W2

open W2C BHH.Cert BHH

/-- The entry bound of a grid: for every table entry `(ir, ir2, d)` the integral of `A_2` over the canonical cell
pair is at most the computed `ā` (`entryF`) times the two cell areas. -/
def EntryBound (g : W2C.Grid) : Prop :=
  ∀ ir ir2 : ℕ, ir < g.NR → ir2 < g.NR → ∀ d : ℤ, |d| < g.NT →
    ∫ p in sector ((gR g).rad ir) ((gR g).rad (ir + 1)) 0 (π / g.NT) ×ˢ
        sector ((gR g).rad ir2) ((gR g).rad (ir2 + 1)) (d * (π / g.NT)) ((d + 1) * (π / g.NT)), A2 p.1 p.2 ≤
      fx (entryF g.prune ((Array.range g.NR).map (mkRing g)) (mkAData g) (mkDData g d) ir ir2).2 *
        (volume (sector ((gR g).rad ir) ((gR g).rad (ir + 1)) 0 (π / g.NT))).toReal *
        (volume (sector ((gR g).rad ir2) ((gR g).rad (ir2 + 1)) (d * (π / g.NT)) ((d + 1) * (π / g.NT)))).toReal

/-- `TableSound` for the run data of a grid, from the entry bound, T1 (rings), T2 (angles), T3 (Lemma 4), T5
(`A_1` radial) and T7 (rotations), and the ring nondegeneracy test `ringOK`. -/
def TableSoundOf : Prop :=
  GreenFormula → RingSound → AngleSound → AngleRange → FrangeSound → A1Radial → RotA2 →
  ∀ (g : W2C.Grid) (dtl : ℕ), 0 < g.N1 → 0 < g.N2 → 2 ≤ g.NT → g.NT ≤ 2 ^ 30 → 0 < g.NSUB →
    (∀ j, j < g.NR → ringOK g j = true) → EntryBound g →
    TableSound (gR g) (discOf g (mkRunData g dtl true).rings (mkRunData g dtl true).tab dtl)

end BHH.W2
