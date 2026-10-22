/-
Rigorous enclosure of the union area of the disks `B(c_i, R)` and of its gradient (`R = 1`), by Green's
formula over the exposed directions (core Lean only; kernel-friendly).

For the circle around `c_i` and the disk around `c_j` (`w = c_j - c_i`, `0 < |w|² < 4R²`), the directions
`t` with `c_i + R u(t)` in the open disk `B°(c_j, R)` are those with `G(t) := 2R⟨u(t), w⟩ - |w|² > 0`, an open
arc of length `< π` (mod 2π).  Around candidate endpoints `θL, θH` (from any source) we certify
`G(θL - ε) < 0 < G(θL + ε)`, `G(θH - ε) > 0 > G(θH + ε)` with `(θH + ε) - (θL - ε) < π`; then the arc lies in
`U = (θL - ε, θH + ε)` and contains `I = [θL + ε, θH - ε]` (mod 2π).  `G(θ ± ε)` comes from `cos θ`, `sin θ`
and the exact bounds `1 - ε²/2 ≤ cos ε ≤ 1`, `ε - ε³/4 ≤ sin ε ≤ ε` by the addition formulas.  The arc of the
circle around `c_j` cut by the disk around `c_i` is the same arc shifted by `π`.  The exposed set `E_i` is
replaced by `E'_i = [0, 2π) \ ⋃ (proxy arcs)`, the proxy arcs `(θL, θH)` (shifted as needed, endpoints moved
by at most a few `piErr ≪ ε`) lying between `I` and `U`; then `E_i Δ E'_i ⊆ ⋃ (U \ I)`, of measure
`≤ 4ε` per arc, and `|∫_{E_i} f - ∫_{E'_i} f| ≤ sup |f| · Σ 4ε`.
-/
import BHHCert.Exact

namespace BHH.Cert

/-- A source of candidate arc endpoints: `(wx, wy, d2, R) ↦ (θL, θH)`, all fixed point (`d2` at scale
`2^-2PR`).  Never trusted. -/
abbrev CandFn := Int → Int → Int → Int → Int × Int

/-- A point of the circle of directions with enclosures of its cosine and sine.  `top = true` is the
endpoint `2π` (cos = 1, sin = 0 exactly); otherwise the point is `t / 2^PR`. -/
structure DirPt where
  t : Int
  top : Bool
  c : Iv
  s : Iv
  deriving Inhabited

/-- An arc piece `(a, b)` of `[0, 2π)` (open; `b` may be the endpoint `2π`). -/
structure Piece where
  a : DirPt
  b : DirPt
  deriving Inhabited

/-- A certified arc: proxy endpoints with cos/sin, and `slack ≥ meas(U \ I)` (fixed point). -/
structure Arc where
  s : DirPt
  e : DirPt
  slack : Int
  deriving Inhabited

/-- `G(θ ± ε)` enclosures from `G0 = 2R⟨u(θ), w⟩` and `H0 = 2R⟨u'(θ), w⟩` (scale `2^-3PR`):
`G(θ ± ε) = cos ε · G0 ± sin ε · H0 - d2`, with `cos ε ∈ [ONE - ce, ONE]`, `sin ε ∈ [e - se, e]`. -/
def gShift (G0 H0 : Int × Int) (d2 e ce se : Int) (plus : Bool) : Int × Int :=
  -- cos ε · G0 (cos ε ∈ [ONE - ce, ONE], positive)
  let cl := ONE - ce
  let aLo := if 0 ≤ G0.1 then G0.1 * cl else G0.1 * ONE
  let aHi := if 0 ≤ G0.2 then G0.2 * ONE else G0.2 * cl
  -- ± sin ε · H0 (sin ε ∈ [e - se, e], positive)
  let sl := e - se
  let hLo := if 0 ≤ H0.1 then H0.1 * sl else H0.1 * e
  let hHi := if 0 ≤ H0.2 then H0.2 * e else H0.2 * sl
  let (bLo, bHi) := if plus then (hLo, hHi) else (-hHi, -hLo)
  -- scale: products are at 2^-4PR; compare with d2 at 2^-2PR -> d2 * ONE^2
  (aLo + bLo - d2 * ONE * ONE, aHi + bHi - d2 * ONE * ONE)

/-- `(2R⟨u(θ), w⟩, 2R⟨u'(θ), w⟩)` with `u' = (-sin, cos)`, scale `2^-3PR`. -/
def gh0 (wx wy R : Int) (c s : Iv) : (Int × Int) × (Int × Int) :=
  let mulI (w : Int) (a : Iv) : Int × Int := if 0 ≤ w then (w * a.lo, w * a.hi) else (w * a.hi, w * a.lo)
  let (x1, x2) := mulI wx c
  let (y1, y2) := mulI wy s
  let (p1, p2) := mulI wx (Iv.neg s)
  let (q1, q2) := mulI wy c
  ((2 * R * (x1 + y1), 2 * R * (x2 + y2)), (2 * R * (p1 + q1), 2 * R * (p2 + q2)))

/-- Try to certify the arc around the candidate endpoints with half-width `e` (fixed point), given the
cos/sin enclosures at the candidates. -/
def certArcWith (wx wy d2 R θL θH : Int) (cL sL cH sH : Iv) (e : Int) : Option Arc :=
  if θL + e ≤ θH - e ∧ (θH + e) - (θL - e) < piLo then
    let ce := shrU (e * e) (PR + 1) + 1          -- ≥ ε²/2
    let se := shrU (e * e * e) (2 * PR + 2) + 1  -- ≥ ε³/4
    let (GL, HL) := gh0 wx wy R cL sL
    let (GH, HH) := gh0 wx wy R cH sH
    let g1 := gShift GL HL d2 e ce se false
    let g2 := gShift GL HL d2 e ce se true
    let g3 := gShift GH HH d2 e ce se false
    let g4 := gShift GH HH d2 e ce se true
    if g1.2 < 0 ∧ 0 < g2.1 ∧ 0 < g3.1 ∧ g4.2 < 0 then
      some ⟨⟨θL, false, cL, sL⟩, ⟨θH, false, cH, sH⟩, 4 * e⟩
    else none
  else none

/-- Half-widths tried, in fixed point: `2^-62`, `2^-44`, `2^-30`, `2^-16`.  Every entry exceeds `4 piErr` (the proxy
endpoints move by at most `3 piErr` under the `π`/`2π` shifts, and the slack is `4ε` per arc). -/
def epsList : List Int := [2 ^ (PR - 62), 2 ^ (PR - 44), 2 ^ (PR - 30), 2 ^ (PR - 16)]

/-- Certify the arc of the circle `c_i` cut by the disk `c_j` (`w = c_j - c_i`), with cos/sin from `cs`. -/
def certArc (cs : Int → Iv × Iv) (wx wy d2 R : Int) (cand : CandFn) : Option Arc :=
  let (θL, θH) := cand wx wy d2 R
  -- range of the candidates: the proxy arcs of circle i start in [-2π, 2π) and those of circle j (shifted by π) too
  if θL.natAbs ≤ 7 * ONE.toNat ∧ θH.natAbs ≤ 7 * ONE.toNat ∧ -(2 * piLo) ≤ θL ∧ θL ≤ piLo then
    let (cL, sL) := cs θL
    let (cH, sH) := cs θH
    epsList.foldl (fun acc e => match acc with
      | some a => some a
      | none => certArcWith wx wy d2 R θL θH cL sL cH sH e) none
  else none

/-! ## moving points on the circle of directions -/

/-- `t + π` (outward rounding chosen by `up`), with cos/sin from those at `t`. -/
def shiftPi (p : DirPt) (up : Bool) : DirPt :=
  ⟨p.t + (if up then piHi else piLo), false, Iv.widen (Iv.neg p.c) piErr, Iv.widen (Iv.neg p.s) piErr⟩

/-- `t + 2π` (`up`: use `2 piHi`, else `2 piLo`) -/
def shift2Pi (p : DirPt) (up : Bool) : DirPt :=
  ⟨p.t + 2 * (if up then piHi else piLo), false, Iv.widen p.c (2 * piErr), Iv.widen p.s (2 * piErr)⟩

/-- `t - 2π` (`up`: use `2 piLo`, i.e. round up; else `2 piHi`) -/
def unshift2Pi (p : DirPt) (up : Bool) : DirPt :=
  ⟨p.t - 2 * (if up then piLo else piHi), false, Iv.widen p.c (2 * piErr), Iv.widen p.s (2 * piErr)⟩

def dirZero : DirPt := ⟨0, false, Iv.int 1, Iv.int 0⟩
def dirTop : DirPt := ⟨0, true, Iv.int 1, Iv.int 0⟩
/-- the point `2 piLo` (just below `2π`) -/
def dirTwoPiLo : DirPt := ⟨2 * piLo, false, Iv.widen (Iv.int 1) (2 * piErr), Iv.widen (Iv.int 0) (2 * piErr)⟩

/-- Pieces of `[0, 2π)` covering the arc `(s, e)` taken mod `2π` (outward), for `-2π < s`, `e - s < π`,
`e < 4π`.  Every non-top endpoint lies in `[0, 2 piLo]`. -/
def normArc (s e : DirPt) : List Piece :=
  if s.t < 0 then
    if s.t + 2 * piLo < 0 then [⟨dirZero, dirTop⟩]
    else if e.t ≤ 0 then
      (if e.t + 2 * piHi ≤ 2 * piLo then [⟨shift2Pi s false, shift2Pi e true⟩]
       else [⟨shift2Pi s false, dirTop⟩])
    else if e.t ≤ 2 * piLo then [⟨shift2Pi s false, dirTop⟩, ⟨dirZero, e⟩]
    else [⟨dirZero, dirTop⟩]
  else if e.t ≤ 2 * piLo then [⟨s, e⟩]
  else if e.t - 2 * piLo ≤ 2 * piLo then
    [⟨if s.t ≤ 2 * piLo then s else dirTwoPiLo, dirTop⟩, ⟨dirZero, unshift2Pi e true⟩]
  else [⟨dirZero, dirTop⟩]

/-- Length (fixed point, upper bound) of a piece. -/
def pieceLen (p : Piece) : Int := Max.max ((if p.b.top then 2 * piHi else p.b.t) - p.a.t) 0

/-! ## integration over the exposed set -/

/-- `p ≤ q` for points of `[0, 2π]` (the top is the largest). -/
def dirLe (p q : DirPt) : Bool := if q.top then true else if p.top then false else p.t ≤ q.t

def insertSorted (p : DirPt) : List DirPt → List DirPt
  | [] => [p]
  | q :: qs => if dirLe p q then p :: q :: qs else q :: insertSorted p qs

def sortDirs : List DirPt → List DirPt
  | [] => []
  | p :: ps => insertSorted p (sortDirs ps)

/-- Is the open interval `(p, q)` inside some piece? -/
def covered (pieces : List Piece) (p q : DirPt) : Bool :=
  pieces.any fun pc => dirLe pc.a p && dirLe q pc.b

/-- The value `t` of a point as an interval (`2π` for the top). -/
def dirVal (p : DirPt) : Iv := if p.top then ⟨2 * piLo, 2 * piHi⟩ else Iv.pt p.t

/-- Contributions of one elementary interval `(p, q)`:
`(∫ (R² + R(cx cos + cy sin))/2, ∫ cos, ∫ sin)`. -/
def elemInt (R cx cy : Int) (p q : DirPt) : Iv × Iv × Iv :=
  let len := Iv.sub (dirVal q) (dirVal p)
  let ds := Iv.sub q.s p.s        -- ∫ cos = sin q - sin p
  let dc := Iv.sub p.c q.c        -- ∫ sin = cos p - cos q
  let R2 := Iv.sqr (Iv.pt R)
  let a := Iv.add (Iv.mul R2 len)
    (Iv.mul (Iv.pt R) (Iv.add (Iv.mul (Iv.pt cx) ds) (Iv.mul (Iv.pt cy) dc)))
  (Iv.div2e a 1, ds, dc)

def sumElems (R cx cy : Int) (pieces : List Piece) : List DirPt → Iv × Iv × Iv
  | p :: q :: rest =>
    let (a, gx, gy) := sumElems R cx cy pieces (q :: rest)
    if covered pieces p q then (a, gx, gy)
    else
      let (a', gx', gy') := elemInt R cx cy p q
      (Iv.add a a', Iv.add gx gx', Iv.add gy gy')
  | _ => (Iv.int 0, Iv.int 0, Iv.int 0)

/-- Area contribution and gradient of circle `i`, from its certified arcs. -/
def circleInt (R cx cy : Int) (arcs : List Arc) : Iv × Iv × Iv :=
  let pieces := arcs.foldr (fun ar acc => normArc ar.s ar.e ++ acc) []
  let slack : Int := arcs.foldr (fun ar acc => ar.slack + acc) 0
  let pts := dirZero :: (pieces.foldr (fun pc acc =>
    (if pc.a.top then acc else pc.a :: (if pc.b.top then acc else pc.b :: acc))) [])
  let sorted := sortDirs pts ++ [dirTop]
  let (a, gx, gy) := sumElems R cx cy pieces sorted
  -- sup |integrand| ≤ (R² + R(|cx| + |cy|))/2 (fixed point, upper bound); slack ≥ 0 expected
  let sl : Int := Max.max slack 0
  let supf : Int := shrU (R * R + R * (cx.natAbs + cy.natAbs : Int)) (PR + 1) + 1
  let errA : Int := shrU (supf * sl) PR + 1
  (Iv.widen a errA, Iv.widen gx sl, Iv.widen gy sl)

/-- Result of the union computation: area and gradient (per point) enclosures. -/
structure UnionRes where
  A : Iv
  gx : List Iv
  gy : List Iv
  deriving Inhabited

/-- Certified arcs of all pairs `i < j` (on the circle of `i`); `none` if two centres coincide or an arc
cannot be certified. -/
def pairArcs (cs : Int → Iv × Iv) (pts : List (Int × Int)) (R : Int) (cand : CandFn) :
    Option (List (Nat × Nat × Arc)) :=
  let n := pts.length
  (List.range n).foldr (fun i acc => match acc with
    | none => none
    | some rest =>
      let ci := pts.getD i (0, 0)
      ((List.range n).filter (fun j => i < j)).foldr (fun j acc2 => match acc2 with
        | none => none
        | some lst =>
          let cj := pts.getD j (0, 0)
          let wx := cj.1 - ci.1
          let wy := cj.2 - ci.2
          let d2 := wx * wx + wy * wy
          if d2 == 0 then none
          else if 4 * R * R ≤ d2 then some lst
          else match certArc cs wx wy d2 R cand with
            | none => none
            | some ar => some ((i, j, ar) :: lst)) (some rest)) (some [])

/-- The arcs on the circle of point `i`. -/
def arcsOf (pa : List (Nat × Nat × Arc)) (i : Nat) : List Arc :=
  pa.foldr (fun (a, b, ar) acc =>
    if a == i then ar :: acc
    else if b == i then ⟨shiftPi ar.s false, shiftPi ar.e true, ar.slack⟩ :: acc
    else acc) []

/-- Union area (radius `R`) and gradient enclosures at the centres `pts`. -/
def unionArea (cs : Int → Iv × Iv) (pts : List (Int × Int)) (R : Int) (cand : CandFn) : Option UnionRes :=
  match pairArcs cs pts R cand with
  | none => none
  | some pa =>
    let res := ((List.range pts.length).zip pts).map fun (i, c) => circleInt R c.1 c.2 (arcsOf pa i)
    some ⟨res.foldl (fun acc r => Iv.add acc r.1) (Iv.int 0), res.map (·.2.1), res.map (·.2.2)⟩

end BHH.Cert
