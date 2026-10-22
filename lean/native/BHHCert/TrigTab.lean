/-
Table-based enclosures of cos and sin (track N speed-up, plan item A1; core Lean).

`cosSinTab t` for `x = t / 2^PR`, `|x| ≤ 7`: write `|x| = j / 2^TB + δ` with `0 ≤ δ < 2^-TB`; the table holds `cosSin`
at the grid points `j / 2^TB` (computed once), `cos δ` and `sin δ` come from `NTT` Taylor terms (instead of 26 terms and
four doublings), and the addition formulas combine them.  Soundness `CosSinSound cosSinTab`: BHH/TrigTab.lean.
-/
import BHHCert.Exact

namespace BHH.Cert

/-- table step `2^-TB` -/
def TB : Nat := 8

/-- Taylor terms for the remainder angle `0 ≤ δ < 2^-TB` -/
def NTT : Nat := 10

/-- `cosSin` at the grid points `j / 2^TB`, `0 ≤ j ≤ 7 · 2^TB` (a closed constant: computed once) -/
def csTable : Array (Iv × Iv) :=
  ((List.range (7 * 2 ^ TB + 1)).map fun (j : Nat) => cosSin ((j : Int) * 2 ^ (PR - TB))).toArray

/-- the trivial enclosure of a cosine and a sine -/
def csTrivial : Iv × Iv := (⟨-ONE, ONE⟩, ⟨-ONE, ONE⟩)

/-- Enclosures of `cos δ`, `sin δ` for `δ = d / 2^PR`, `|δ| ≤ 1`, by `NTT` Taylor terms and the remainder bound -/
def sinCosTiny (d : Int) : Iv × Iv :=
  let (c, s, last) := taylorGo d 0 NTT (NTT + 1) 0 (Iv.int 1) ⟨0, 0⟩ ⟨0, 0⟩
  let mag := Max.max (Int.natAbs last.lo) (Int.natAbs last.hi)
  let rem : Int := divU (mag * (NTT + 1)) NTT + 1
  (Iv.widen c rem, Iv.widen s rem)

/-- table-based enclosures of `(cos x, sin x)`, `x = t / 2^PR`, `|x| ≤ 7` (trivial enclosures otherwise) -/
def cosSinTab (t : Int) : Iv × Iv :=
  if t.natAbs ≤ 7 * ONE.toNat then
    let j := t.natAbs >>> (PR - TB)
    let d : Int := (t.natAbs : Int) - (j : Int) * 2 ^ (PR - TB)
    let e := csTable.getD j csTrivial
    let cd := (sinCosTiny d).1
    let sd := (sinCosTiny d).2
    let c := Iv.sub (Iv.mul e.1 cd) (Iv.mul e.2 sd)
    let s := Iv.add (Iv.mul e.2 cd) (Iv.mul e.1 sd)
    (clip1 c, clip1 (if t < 0 then Iv.neg s else s))
  else csTrivial

end BHH.Cert
