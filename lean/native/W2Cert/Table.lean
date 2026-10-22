/-
Window-2 tables in exact fixed-point interval arithmetic (core Lean only): per-ring data and, for every
`(ir, ir', d)`, the class of the edge `{i+1, i-1}` (Lemma 4 on the actual cells) and an upper bound `ā_2` for the
mean of `A_2(w, z) = |B(z) \ (B(0) ∪ B(-w))|` over the cell pair (vertex lemma at a rounded centroid, or the fallback
`A_2 ≤ A_1(|z|)`), as in the frozen evaluator `w2_arb_386c4097.c` (Part A), with optional vertex pruning.

Cells: radii `r_j = j/N1` (`j ≤ N1`), `1 + (j - N1)/N2` (`j ≥ N1`); angles `[it·dθ, (it+1)·dθ] - π/2`, `dθ = π/NT`.
The table for `(ir, ir', d)` is computed for the z-cell at angles `[0, dθ]` and the z'-cell at `[d dθ, (d+1) dθ]`.
-/
import BHHCert.Union
import W2Cert.Fix

namespace W2C
open BHH.Cert

/-- Grid parameters. -/
structure Grid where
  N1 : Nat
  N2 : Nat
  NT : Nat
  NSUB : Nat
  prune : Bool
  deriving Repr, Inhabited

namespace Grid
def NR (g : Grid) : Nat := g.N1 + g.N2
def ND (g : Grid) : Nat := 2 * g.NT - 1
end Grid

/-- `⌊a/b⌋`, `⌈a/b⌉` as an interval for the rational `a/b` (`b > 0`), fixed point. -/
def ratIv (a : Int) (b : Nat) : Iv := ⟨divD (a * ONE) b, divU (a * ONE) b⟩

/-- the radius `r_j` -/
def radIv (g : Grid) (j : Nat) : Iv :=
  if j ≤ g.N1 then ratIv j g.N1 else Iv.add (Iv.int 1) (ratIv (j - g.N1) g.N2)

/-- `dθ = π/NT` -/
def dthIv (g : Grid) : Iv := ⟨divD piLo g.NT, divU piHi g.NT⟩

/-- `cos` of an angle interval `[a.lo, a.hi]` inside `(-2π, 2π)` of width `< π/2`: the endpoint values, widened to
`1` if the interval may contain `0` and to `-1` if it may contain `±π`. -/
def cosIvG (a : Iv) : Iv :=
  let c1 := (cosSin a.lo).1
  let c2 := (cosSin a.hi).1
  let lo := if (a.lo ≤ piHi ∧ piLo ≤ a.hi) ∨ (a.lo ≤ -piLo ∧ -piHi ≤ a.hi) then -ONE else Min.min c1.lo c2.lo
  let hi := if a.lo ≤ 0 ∧ 0 ≤ a.hi then ONE else Max.max c1.hi c2.hi
  ⟨lo, hi⟩

/-- `sin` of an angle interval inside `(-2π, 2π)` of width `< π/2`: the endpoint values, widened to `1` if the
interval may contain `π/2` and to `-1` if it may contain `-π/2`. -/
def sinIvG (a : Iv) : Iv :=
  let s1 := (cosSin a.lo).2
  let s2 := (cosSin a.hi).2
  let lo := if a.lo ≤ -halfPiLo ∧ -halfPiHi ≤ a.hi then -ONE else Min.min s1.lo s2.lo
  let hi := if a.lo ≤ halfPiHi ∧ halfPiLo ≤ a.hi then ONE else Max.max s1.hi s2.hi
  ⟨lo, hi⟩

/-- `cos` of an angle interval inside `[0, π]` (decreasing). -/
def cosIvDec (a : Iv) : Iv := ⟨(cosSin a.hi).1.lo, (cosSin a.lo).1.hi⟩

/-- `cos(k dθ)` for `0 ≤ k ≤ NT` (`cos 0 = 1`, `cos π = -1` exactly). -/
def cosK (g : Grid) (k : Nat) : Iv :=
  if k == 0 then Iv.int 1
  else if k == g.NT then Iv.int (-1)
  else cosIvDec (Iv.mulNat (dthIv g) k)

/-- Per-ring data. -/
structure Ring where
  r1 : Iv
  r2 : Iv
  areaLo : Int      -- lower bound of the cell area (r2² - r1²) dθ / 2
  euLo : Int        -- lower bound of E A_1(|z|) over the ring (density ∝ r)
  euHi : Int        -- upper bound of the same
  rhoc : Iv         -- centroid radius (2/3)(r2³ - r1³)/(r2² - r1²) · sin(dθ/2)/(dθ/2)
  momHi : Int       -- upper bound of the second moment about the centroid (r1² + r2²)/2 - rhoc²
  nflag : Bool      -- r2 ≤ 1 (the edge {i+1, i} is present)
  deriving Inhabited

/-- Riemann sums of `E A_1(|z|)` over `[r1, r2]` with density `∝ r`: `(lower, upper)`; sub-interval `l` has mass
`(b² - a²)/(r2² - r1²)`, `a = r1 + (r2 - r1) l / n`. Exact rationals `r = num/den` are passed as intervals. -/
def euRing (g : Grid) (j : Nat) : Int × Int :=
  let r1 := radIv g j
  let r2 := radIv g (j + 1)
  let n := g.NSUB
  let den := Iv.sub (Iv.sqr r2) (Iv.sqr r1)
  let pt (l : Nat) : Iv := Iv.add r1 (Iv.divNat (Iv.mulNat (Iv.sub r2 r1) l) n)
  (List.range n).foldl (fun (acc : Int × Int) l =>
    let a := pt l
    let b := pt (l + 1)
    let w := Iv.div (Iv.sub (Iv.sqr b) (Iv.sqr a)) den
    let wlo := Max.max w.lo 0
    let ua := (a1Iv a).lo
    let ub := (a1Iv b).hi
    (acc.1 + shrD (wlo * Max.max ua 0) PR, acc.2 + shrU (w.hi * ub) PR)) (0, 0)

/-- Ring `j` (cells between `r_j` and `r_{j+1}`). -/
def mkRing (g : Grid) (j : Nat) : Ring :=
  let r1 := radIv g j
  let r2 := radIv g (j + 1)
  let dth := dthIv g
  let area := Iv.div2e (Iv.mul (Iv.sub (Iv.sqr r2) (Iv.sqr r1)) dth) 1
  let (elo, ehi) := euRing g j
  let half := Iv.div2e dth 1
  let sinc := Iv.div (sinIvG half) half
  let r23 := Iv.sub (Iv.mul (Iv.sqr r2) r2) (Iv.mul (Iv.sqr r1) r1)
  let r22 := Iv.sub (Iv.sqr r2) (Iv.sqr r1)
  let rhoc := Iv.mul (Iv.divNat (Iv.mulNat (Iv.div r23 r22) 2) 3) sinc
  let mom := Iv.sub (Iv.div2e (Iv.add (Iv.sqr r1) (Iv.sqr r2)) 1) (Iv.sqr rhoc)
  ⟨r1, r2, area.lo, elo, ehi, rhoc, Max.max mom.hi 0, decide (j + 1 ≤ g.N1)⟩

/-- Lemma 4: `[fmin, fmax]` enclosing `r² + r'² + 2 r r' c` for `r ∈ [r1, r2]`, `r' ∈ [q1, q2]`, `c ∈ [cmin, cmax]`
(as lower bound of the minimum and upper bound of the maximum). -/
def frange (r1 r2 q1 q2 cmin cmax : Iv) : Int × Int :=
  let corners : List (Iv × Iv) := [(r1, q1), (r1, q2), (r2, q1), (r2, q2)]
  let fval (r q c : Iv) : Iv := Iv.add (Iv.add (Iv.sqr r) (Iv.sqr q)) (Iv.mul2e (Iv.mul (Iv.mul r q) c) 1)
  let fmax := corners.foldl (fun m (r, q) => Max.max m (fval r q cmax).hi) (fval r1 q1 cmax).hi
  let fmin0 := corners.foldl (fun m (r, q) => Min.min m (fval r q cmin).lo) (fval r1 q1 cmin).lo
  let fmin :=
    if 0 ≤ cmin.lo then fmin0
    else
      let oneC2 := Iv.sub (Iv.int 1) (Iv.sqr cmin)
      let edges : List (Iv × Iv × Iv) := [(r1, q1, q2), (r2, q1, q2), (q1, r1, r2), (q2, r1, r2)]
      edges.foldl (fun m (fx, olo, ohi) =>
        let x := Iv.neg (Iv.mul cmin fx)
        if x.hi < olo.lo ∨ ohi.hi < x.lo then m
        else Min.min m (Iv.mul (Iv.sqr fx) oneC2).lo) fmin0
  (fmin, fmax)

/-- `(cmin, cmax)`: the range of `cos φ` for `φ ∈ [(|d|-1) dθ, (|d|+1) dθ]`. -/
def cosRange (g : Grid) (d : Int) : Iv × Iv :=
  let ad := d.natAbs
  let cmax := if ad ≤ 1 then Iv.int 1 else cosK g (ad - 1)
  let cmin := cosK g (ad + 1)
  (cmin, cmax)

/-- Float candidates for arc endpoints of the union area, refined by one Newton step on
`G(θ) = 2R⟨u(θ), w⟩ - |w|²` with the verified `cos`/`sin` midpoints (untrusted). -/
def unionCand : CandFn := fun wx wy d2 R =>
  let fx := toF wx
  let fy := toF wy
  let d := Float.sqrt (fx * fx + fy * fy)
  let fR := toF R
  let psi := Float.atan2 fy fx
  let x := d / (2 * fR)
  let al := Float.acos (if x > 1 then 1 else x)
  let newton (θ : Int) : Int :=
    let cs := cosSin θ
    let c := ivMid cs.1
    let s := ivMid cs.2
    -- G at scale 2^-2PR (d2 is at 2^-2PR), G' likewise
    let G := 2 * R * (wx * c + wy * s) / ONE - d2
    let G' := 2 * R * (wy * c - wx * s) / ONE
    if G' == 0 then θ else θ - (G * ONE) / G'
  (newton (ofF (psi - al)), newton (ofF (psi + al)))

/-- round an interval to an exact fixed-point number near its midpoint -/
def midPt (a : Iv) : Int := (a.lo + a.hi) / 2

/-- Upper bound for `|p - q|` where `p` is an interval point and `q` an exact point. -/
def distHi (px py : Iv) (qx qy : Int) : Int :=
  (Iv.sqrt (Iv.add (Iv.sqr (Iv.sub px (Iv.pt qx))) (Iv.sqr (Iv.sub py (Iv.pt qy))))).hi

/-- Angle data that depend only on the offset `d`: the `cos φ` range and the direction of the z'-cell centroid. -/
structure DData where
  cmin : Iv
  cmax : Iv
  cx : Iv      -- cos((2d+1) dθ/2)
  sy : Iv      -- sin((2d+1) dθ/2)
  deriving Inhabited

/-- Angle data shared by all entries: `cos(dθ/2)`, `sin(dθ/2)`. -/
structure AData where
  ch : Iv
  sh : Iv
  deriving Inhabited

def mkAData (g : Grid) : AData :=
  let ang0 := Iv.div2e (dthIv g) 1
  ⟨cosIvG ang0, sinIvG ang0⟩

def mkDData (g : Grid) (d : Int) : DData :=
  let (cmin, cmax) := cosRange g d
  let ang2 := Iv.div2e (Iv.mul (dthIv g) (Iv.int (2 * d + 1))) 1
  ⟨cmin, cmax, cosIvG ang2, sinIvG ang2⟩

/-- `dd[d + NT - 1] = mkDData g d` for `d ∈ [-(NT-1), NT-1]`. -/
def mkDTab (g : Grid) : Array DData :=
  (Array.range g.ND).map fun (di : Nat) => mkDData g (Int.ofNat di - Int.ofNat (g.NT - 1))

/-- Upper bound for `max_{z ∈ cell} |z - c̄|` (attained at a corner `(r, ±dθ/2)`), `c̄` the centroid. -/
def epsCell (R : Ring) (ch : Iv) : Int :=
  let f (r : Iv) : Int := (Iv.add (Iv.sqr r) (Iv.sub (Iv.sqr R.rhoc) (Iv.mul2e (Iv.mul (Iv.mul r R.rhoc) ch) 1))).hi
  let m := Max.max (f R.r1) (f R.r2)
  (Iv.sqrt ⟨Max.max m 0, Max.max m 0⟩).hi + 1

/-- Upper bound for `|P - c_l|` for each vertex `P` of the pair `(a, b)` (exact centres, `0 < |b - a| < 2`):
`P = a + w/2 ± s (-w.2, w.1)`, `w = b - a`, `s = √(1 - |w|²/4)/|w|`. -/
def vertexDistHi (ax ay bx by_ lx ly : Int) : Int × Int :=
  let wx := bx - ax
  let wy := by_ - ay
  let d2 : Iv := Iv.add (Iv.sqr (Iv.pt wx)) (Iv.sqr (Iv.pt wy))
  let dc := Iv.sqrt d2
  let s := Iv.div (Iv.sqrt (Iv.sub (Iv.int 1) (Iv.div2e d2 2))) dc
  let mx := Iv.add (Iv.pt ax) (Iv.div2e (Iv.pt wx) 1)
  let my := Iv.add (Iv.pt ay) (Iv.div2e (Iv.pt wy) 1)
  let ox := Iv.mul s (Iv.pt (-wy))
  let oy := Iv.mul s (Iv.pt wx)
  let dist (px py : Iv) : Int :=
    (Iv.sqrt (Iv.add (Iv.sqr (Iv.sub px (Iv.pt lx))) (Iv.sqr (Iv.sub py (Iv.pt ly))))).hi
  (dist (Iv.add mx ox) (Iv.add my oy), dist (Iv.sub mx ox) (Iv.sub my oy))

/-- One table entry with precomputed angle data (same value as `entry`). -/
def entryF (prune : Bool) (rings : Array Ring) (ad : AData) (dd : DData) (ir ir2 : Nat) : Nat × Int :=
  let R1 := rings[ir]!
  let R2 := rings[ir2]!
  let (r1, r2, q1, q2) := (R1.r1, R1.r2, R2.r1, R2.r2)
  let (cmin, cmax) := (dd.cmin, dd.cmax)
  let (fmin, fmax) := frange r1 r2 q1 q2 cmin cmax
  let cls : Nat := if fmax ≤ ONE then 1 else if ONE < fmin then 0 else 2
  let fb := R2.euHi
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
  match BHH.Cert.unionArea cosSin [(p0x, p0y), (0, 0), (p2x, p2y)] ONE unionCand with
  | none => (cls, fb)
  | some ur =>
    let A3hi := ur.A.hi
    let ch := ad.ch
    let r1h := Iv.mul r1 ch
    let q1h := Iv.mul q1 ch
    let (hmin, hmax) := frange r1h r2 q1h q2 cmin cmax
    let eps01 := e0 + 1
    let eps12 := e2 + 1
    let eps02 := e0 + e2 + 1
    let dmn : List Int := [r1h.lo - eps01, q1h.lo - eps12,
                           (Iv.sqrt ⟨Max.max hmin 0, Max.max hmin 0⟩).lo - eps02]
    let dmx : List Int := [r2.hi + eps01, q2.hi + eps12, (Iv.sqrt ⟨hmax, hmax⟩).hi + eps02]
    let m0 := R1.momHi + shrU (e0 * e0) PR + 1
    let m2 := R2.momHi + shrU (e2 * e2) PR + 1
    let sq0 := (Iv.sqrt ⟨m0, m0⟩).hi
    let sq2 := (Iv.sqrt ⟨m2, m2⟩).hi
    let S1s : List Int := [sq0, sq2, sq0 + sq2]
    let S2s : List Int := [m0, m2, m0 + m2 + 2 * shrU (sq0 * sq2) PR + 2]
    let pairs : List Nat := [0, 1, 2]
    -- pair p: 0 = (y0, y1), 1 = (y1, y2), 2 = (y0, y2); third point l; endpoints of the pair (i, j)
    let pts : List (Int × Int) := [(p0x, p0y), (0, 0), (p2x, p2y)]
    let epsPt : List Int := if prune then [epsCell R1 ch + e0 + 1, 0, epsCell R2 ch + e2 + 1] else [0, 0, 0]
    let er? : Option Int := pairs.foldl (fun acc p => match acc with
      | none => none
      | some er =>
        let dn := dmn.getD p 0
        let dx := dmx.getD p 0
        if 2 * ONE ≤ dn then some er
        else if dn ≤ 0 then none
        else
          let S1 := S1s.getD p 0
          let S2 := S2s.getD p 0
          let dxIv : Iv := ⟨dx, dx⟩
          let dnIv : Iv := ⟨dn, dn⟩
          let dx2 := Iv.sqr dxIv
          let useFirst := dx * 100 < 198 * ONE ∧ dx2.hi < 4 * ONE
          let lam : Int := if useFirst then (Iv.inv (Iv.sqrt (Iv.sub (Iv.int 4) dx2))).hi else 0
          let mu : Int :=
            if useFirst then 0
            else
              let u := if dx < 2 * ONE then (asinIv (Iv.div2e dxIv 1)).hi else halfPiHi
              let w := (asinIv (Iv.div2e dnIv 1)).lo
              Max.max (2 * (u - w)) 0
          let rad : Int := if useFirst then shrU (lam * S2) PR + 1 else shrU (mu * S1) PR + 1
          let tang := Min.min ((Iv.div ⟨S2, S2⟩ dnIv).hi) (shrU (piHi * S1) PR + 1)
          -- vertex pruning (Remark 3.2): ν = number of vertices at c not certified covered by the third disk
          let nu : Nat :=
            if !prune then 2 else
            let (i, j, l) : Nat × Nat × Nat := if p == 0 then (0, 1, 2) else if p == 1 then (1, 2, 0) else (0, 2, 1)
            let (ax, ay) := pts.getD i (0, 0)
            let (bx, by_) := pts.getD j (0, 0)
            let (lx, ly) := pts.getD l (0, 0)
            let dc2 := (bx - ax) * (bx - ax) + (by_ - ay) * (by_ - ay)
            if 0 < dc2 ∧ dc2 < 4 * ONE * ONE then
              let ei := epsPt.getD i 0
              let ej := epsPt.getD j 0
              let el := epsPt.getD l 0
              let wv := ei + ej
              -- T(ε_i + ε_j) = λ w + μ + min(w/d⁻, π), upper bound
              let tT : Int := shrU (lam * wv) PR + 1 + mu + Min.min ((Iv.div ⟨wv, wv⟩ dnIv).hi) piHi
              let (d1, d2) := vertexDistHi ax ay bx by_ lx ly
              (if d1 + ei + tT + el < ONE then 0 else 1) + (if d2 + ei + tT + el < ONE then 0 else 1)
            else 2
          some (er + nu * (rad + tang))) (some 0)
    match er? with
    | none => (cls, fb)
    | some er =>
      let lv := A3hi + 2 * (e0 + e2) + er - (piLo + R1.euLo) + 2
      (cls, Min.min fb lv)

/-- One table entry: `(class, ā_2 upper bound)`; class `1` sure present, `0` sure absent, `2` unknown. -/
def entry (g : Grid) (rings : Array Ring) (ir ir2 : Nat) (d : Int) : Nat × Int :=
  let R1 := rings[ir]!
  let R2 := rings[ir2]!
  let (r1, r2, q1, q2) := (R1.r1, R1.r2, R2.r1, R2.r2)
  let (cmin, cmax) := cosRange g d
  let (fmin, fmax) := frange r1 r2 q1 q2 cmin cmax
  let cls : Nat := if fmax ≤ ONE then 1 else if ONE < fmin then 0 else 2
  let fb := R2.euHi
  -- expansion point: -C_Z (z-cell at angles [0, dθ]) and C_Z' (z'-cell at [d dθ, (d+1) dθ])
  let dth := dthIv g
  let ang0 := Iv.div2e dth 1
  let ang2 := Iv.div2e (Iv.mul dth (Iv.int (2 * d + 1))) 1
  let cz0x := Iv.mul R1.rhoc (cosIvG ang0)
  let cz0y := Iv.mul R1.rhoc (sinIvG ang0)
  let cz2x := Iv.mul R2.rhoc (cosIvG ang2)
  let cz2y := Iv.mul R2.rhoc (sinIvG ang2)
  let p0x := -(midPt cz0x)
  let p0y := -(midPt cz0y)
  let p2x := midPt cz2x
  let p2y := midPt cz2y
  let e0 := distHi cz0x cz0y (-p0x) (-p0y)
  let e2 := distHi cz2x cz2y p2x p2y
  match BHH.Cert.unionArea cosSin [(p0x, p0y), (0, 0), (p2x, p2y)] ONE unionCand with
  | none => (cls, fb)
  | some ur =>
    let A3hi := ur.A.hi
    let ch := cosIvDec ang0
    let r1h := Iv.mul r1 ch
    let q1h := Iv.mul q1 ch
    let (hmin, hmax) := frange r1h r2 q1h q2 cmin cmax
    let eps01 := e0 + 1
    let eps12 := e2 + 1
    let eps02 := e0 + e2 + 1
    -- pair 0: (Y0, Y1) |z|; pair 1: (Y1, Y2) |z'|; pair 2: (Y0, Y2) |z + z'|
    let dmn : List Int := [r1h.lo - eps01, q1h.lo - eps12,
                           (Iv.sqrt ⟨Max.max hmin 0, Max.max hmin 0⟩).lo - eps02]
    let dmx : List Int := [r2.hi + eps01, q2.hi + eps12, (Iv.sqrt ⟨hmax, hmax⟩).hi + eps02]
    let m0 := R1.momHi + shrU (e0 * e0) PR + 1
    let m2 := R2.momHi + shrU (e2 * e2) PR + 1
    let sq0 := (Iv.sqrt ⟨m0, m0⟩).hi
    let sq2 := (Iv.sqrt ⟨m2, m2⟩).hi
    let S1s : List Int := [sq0, sq2, sq0 + sq2]
    let S2s : List Int := [m0, m2, m0 + m2 + 2 * shrU (sq0 * sq2) PR + 2]
    let pairs : List Nat := [0, 1, 2]
    let er? : Option Int := pairs.foldl (fun acc p => match acc with
      | none => none
      | some er =>
        let dn := dmn.getD p 0
        let dx := dmx.getD p 0
        if 2 * ONE ≤ dn then some er
        else if dn ≤ 0 then none
        else
          let S1 := S1s.getD p 0
          let S2 := S2s.getD p 0
          let dxIv : Iv := ⟨dx, dx⟩
          let dnIv : Iv := ⟨dn, dn⟩
          let dx2 := Iv.sqr dxIv
          -- first choice (λ = 1/√(4 - d⁺²)) when d⁺ < 1.98, else the second
          let useFirst := dx * 100 < 198 * ONE ∧ dx2.hi < 4 * ONE
          let rad : Int :=
            if useFirst then
              let lam := Iv.inv (Iv.sqrt (Iv.sub (Iv.int 4) dx2))
              shrU (lam.hi * S2) PR + 1
            else
              let u := if dx < 2 * ONE then (asinIv (Iv.div2e dxIv 1)).hi else halfPiHi
              let w := (asinIv (Iv.div2e dnIv 1)).lo
              let mu := 2 * (u - w)
              shrU (Max.max mu 0 * S1) PR + 1
          let tang := Min.min ((Iv.div ⟨S2, S2⟩ dnIv).hi) (shrU (piHi * S1) PR + 1)
          let nu : Nat := 2
          some (er + nu * (rad + tang))) (some 0)
    match er? with
    | none => (cls, fb)
    | some er =>
      let lv := A3hi + 2 * (e0 + e2) + er - (piLo + R1.euLo) + 2
      (cls, Min.min fb lv)

end W2C
