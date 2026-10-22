/-
`W2C.entryF` restated with named parts (`entryG`, equal by `rfl`): the expansion-point data `ECore`, the per-pair
step `pairStep` of the remainder fold, and the nondegeneracy test `entryOK` (no `Iv.inv`/`Iv.div` by an interval
whose lower end is `≤ 0` on the path taken).
-/
import W2Cert.Table

namespace W2C
open BHH.Cert

/-- The data of the vertex path of an entry. -/
structure ECore where
  p0x : Int
  p0y : Int
  p2x : Int
  p2y : Int
  e0 : Int
  e2 : Int
  dmn : List Int
  dmx : List Int
  S1s : List Int
  S2s : List Int
  pts : List (Int × Int)
  epsR : List Int

/-- The expansion point (rounded centroids `-c̄_Z`, `0`, `c̄_Z'`), the distance bounds, moments and vertex radii. -/
def mkECore (rings : Array Ring) (ad : AData) (dd : DData) (ir ir2 : Nat) : ECore :=
  let R1 := rings[ir]!
  let R2 := rings[ir2]!
  let cz0x := Iv.mul R1.rhoc ad.ch
  let cz0y := Iv.mul R1.rhoc ad.sh
  let cz2x := Iv.mul R2.rhoc dd.cx
  let cz2y := Iv.mul R2.rhoc dd.sy
  let p0x := -(midPt cz0x)
  let p0y := -(midPt cz0y)
  let p2x := midPt cz2x
  let p2y := midPt cz2y
  let e0 := distHi cz0x cz0y (-p0x) (-p0y)
  let e2 := distHi cz2x cz2y p2x p2y
  let ch := ad.ch
  let r1h := Iv.mul R1.r1 ch
  let q1h := Iv.mul R2.r1 ch
  let hh := frange r1h R1.r2 q1h R2.r2 dd.cmin dd.cmax
  let eps01 := e0 + 1
  let eps12 := e2 + 1
  let eps02 := e0 + e2 + 1
  let m0 := R1.momHi + shrU (e0 * e0) PR + 1
  let m2 := R2.momHi + shrU (e2 * e2) PR + 1
  let sq0 := (Iv.sqrt ⟨m0, m0⟩).hi
  let sq2 := (Iv.sqrt ⟨m2, m2⟩).hi
  ⟨p0x, p0y, p2x, p2y, e0, e2,
   [r1h.lo - eps01, q1h.lo - eps12, (Iv.sqrt ⟨Max.max hh.1 0, Max.max hh.1 0⟩).lo - eps02],
   [R1.r2.hi + eps01, R2.r2.hi + eps12, (Iv.sqrt ⟨hh.2, hh.2⟩).hi + eps02],
   [sq0, sq2, sq0 + sq2], [m0, m2, m0 + m2 + 2 * shrU (sq0 * sq2) PR + 2],
   [(p0x, p0y), (0, 0), (p2x, p2y)],
   [epsCell R1 ch + e0 + 1, 0, epsCell R2 ch + e2 + 1]⟩

/-- the first choice `(λ, μ) = (1/√(4 - d⁺²), 0)` is taken -/
abbrev useFirstOf (dx : Int) : Prop := dx * 100 < 198 * ONE ∧ (Iv.sqr ⟨dx, dx⟩).hi < 4 * ONE

/-- `λ` (upper bound, `0` for the second choice) -/
def lamOf (dx : Int) : Int :=
  if useFirstOf dx then (Iv.inv (Iv.sqrt (Iv.sub (Iv.int 4) (Iv.sqr ⟨dx, dx⟩)))).hi else 0

/-- `μ` (upper bound, `0` for the first choice) -/
def muOf (dn dx : Int) : Int :=
  if useFirstOf dx then 0
  else
    let u := if dx < 2 * ONE then (asinIv (Iv.div2e ⟨dx, dx⟩ 1)).hi else halfPiHi
    let w := (asinIv (Iv.div2e ⟨dn, dn⟩ 1)).lo
    Max.max (2 * (u - w)) 0

/-- the endpoints `(i, j)` and the third point `l` of pair `p` -/
def pairIJL (p : Nat) : Nat × Nat × Nat := if p == 0 then (0, 1, 2) else if p == 1 then (1, 2, 0) else (0, 2, 1)

/-- `ν` of pair `p` (vertex pruning, Remark 3.2) -/
def nuOf (prune : Bool) (pts : List (Int × Int)) (epsPt : List Int) (lam mu dn : Int) (p : Nat) : Nat :=
  if !prune then 2 else
  let (i, j, l) := pairIJL p
  let (ax, ay) := pts.getD i (0, 0)
  let (bx, by_) := pts.getD j (0, 0)
  let (lx, ly) := pts.getD l (0, 0)
  let dc2 := (bx - ax) * (bx - ax) + (by_ - ay) * (by_ - ay)
  if 0 < dc2 ∧ dc2 < 4 * ONE * ONE then
    let ei := epsPt.getD i 0
    let ej := epsPt.getD j 0
    let el := epsPt.getD l 0
    let wv := ei + ej
    let tT : Int := shrU (lam * wv) PR + 1 + mu + Min.min ((Iv.div ⟨wv, wv⟩ ⟨dn, dn⟩).hi) piHi
    let (d1, d2) := vertexDistHi ax ay bx by_ lx ly
    (if d1 + ei + tT + el < ONE then 0 else 1) + (if d2 + ei + tT + el < ONE then 0 else 1)
  else 2

/-- One step of the remainder fold of `entryF` (pair `p`). -/
def pairStep (prune : Bool) (C : ECore) (acc : Option Int) (p : Nat) : Option Int :=
  match acc with
  | none => none
  | some er =>
    let dn := C.dmn.getD p 0
    let dx := C.dmx.getD p 0
    if 2 * ONE ≤ dn then some er
    else if dn ≤ 0 then none
    else
      let S1 := C.S1s.getD p 0
      let S2 := C.S2s.getD p 0
      let lam := lamOf dx
      let mu := muOf dn dx
      let rad : Int := if useFirstOf dx then shrU (lam * S2) PR + 1 else shrU (mu * S1) PR + 1
      let tang := Min.min ((Iv.div ⟨S2, S2⟩ ⟨dn, dn⟩).hi) (shrU (piHi * S1) PR + 1)
      some (er + (nuOf prune C.pts (if prune then C.epsR else [0, 0, 0]) lam mu dn p : Int) * (rad + tang))

/-- `entryF`, restated. -/
def entryG (prune : Bool) (rings : Array Ring) (ad : AData) (dd : DData) (ir ir2 : Nat) : Nat × Int :=
  let R1 := rings[ir]!
  let R2 := rings[ir2]!
  let ff := frange R1.r1 R1.r2 R2.r1 R2.r2 dd.cmin dd.cmax
  let cls : Nat := if ff.2 ≤ ONE then 1 else if ONE < ff.1 then 0 else 2
  let fb := R2.euHi
  let C := mkECore rings ad dd ir ir2
  match BHH.Cert.unionArea cosSin C.pts ONE unionCand with
  | none => (cls, fb)
  | some ur =>
    match [0, 1, 2].foldl (pairStep prune C) (some 0) with
    | none => (cls, fb)
    | some er =>
      let lv := ur.A.hi + 2 * (C.e0 + C.e2) + er - (piLo + R1.euLo) + 2
      (cls, Min.min fb lv)

/-- The tests of one pair on the path taken: positive lower ends of the interval denominators. -/
def pairOK (prune : Bool) (C : ECore) (p : Nat) : Bool :=
  let dn := C.dmn.getD p 0
  let dx := C.dmx.getD p 0
  if 2 * ONE ≤ dn ∨ dn ≤ 0 then true
  else
    (!decide (useFirstOf dx) || decide (0 < (Iv.sqrt (Iv.sub (Iv.int 4) (Iv.sqr ⟨dx, dx⟩))).lo)) &&
    (!prune ||
      let (i, j, _) := pairIJL p
      let (ax, ay) := C.pts.getD i (0, 0)
      let (bx, by_) := C.pts.getD j (0, 0)
      let dc2 := (bx - ax) * (bx - ax) + (by_ - ay) * (by_ - ay)
      !decide (0 < dc2 ∧ dc2 < 4 * ONE * ONE) ||
        decide (0 < (Iv.sqrt (Iv.add (Iv.sqr (Iv.pt (bx - ax))) (Iv.sqr (Iv.pt (by_ - ay))))).lo))

/-- The nondegeneracy test of an entry (only the vertex path matters). -/
def entryOK (prune : Bool) (rings : Array Ring) (ad : AData) (dd : DData) (ir ir2 : Nat) : Bool :=
  let C := mkECore rings ad dd ir ir2
  match BHH.Cert.unionArea cosSin C.pts ONE unionCand with
  | none => true
  | some _ => pairOK prune C 0 && pairOK prune C 1 && pairOK prune C 2

/-- The nondegeneracy test of a ring (positive interval denominators in `mkRing`). -/
def ringOK (g : Grid) (j : Nat) : Bool :=
  decide (0 < (Iv.sub (Iv.sqr (radIv g (j + 1))) (Iv.sqr (radIv g j))).lo) && decide (0 < (Iv.div2e (dthIv g) 1).lo)

/-- All rings and all table entries of a grid pass the nondegeneracy tests (rows of entries in parallel). -/
def nondegOK (g : Grid) : Bool :=
  let rings := (Array.range g.NR).map (mkRing g)
  let ad := mkAData g
  let dtab := mkDTab g
  (List.range g.NR).all (ringOK g) &&
    (((List.range g.NR).map fun ir => Task.spawn fun _ =>
        (List.range (g.NR * g.ND)).all fun q => entryOK g.prune rings ad dtab[q % g.ND]! ir (q / g.ND)).all
      Task.get)

end W2C
