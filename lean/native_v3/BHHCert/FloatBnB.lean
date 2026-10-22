/-
Port of the float search program box_ck14 (frozen copy box_ck14_6feb4deb.c) to Lean `Float`.

This code only DECIDES which boxes are split, dropped or scored (and computes the float leaf values used
for the "skip leaves of float value 0" rule).  It is never part of a proof: the soundness theorem of the
branch and bound holds for every decision function.  The aim is bit-identical decisions with the C program
(same IEEE double operations in the same order, same libm functions), so that the leaf set is the paper's.
-/

namespace BHH.Cert.Flt

/-- `M_PI` -/
def fpi : Float := Float.ofBits 0x400921FB54442D18
/-- `2 * M_PI` -/
def f2pi : Float := 2 * fpi

/-- Parameters and tables of a run. -/
structure Ctx where
  k : Nat
  m : Nat
  npairs : Nat
  pi_ : Array Nat
  pj_ : Array Nat
  W0 : Float
  WF : Float
  EPS : Float
  sexp : Float
  PREF : Float
  gmin3 : Array Int
  gmax3 : Array Int
  pow3 : Array Nat

/-! ## geometry (union_area_grad) -/

/-- insertion sort of the arcs by start (as in box_ck14: stable, strict `>` comparison) -/
def sortArcs (L H : Array Float) : Array Float × Array Float := Id.run do
  let mut L := L
  let mut H := H
  let q := L.size
  for s in [1:q] do
    let a0 := L[s]!
    let b0 := H[s]!
    let mut r : Int := (s : Int) - 1
    while r ≥ 0 && L[r.toNat]! > a0 do
      L := L.set! (r.toNat + 1) L[r.toNat]!
      H := H.set! (r.toNat + 1) H[r.toNat]!
      r := r - 1
    L := L.set! ((r + 1).toNat) a0
    H := H.set! ((r + 1).toNat) b0
  return (L, H)

/-- `union_area_grad`: union area of the unit disks and its gradient (float). -/
def unionAreaGrad (k : Nat) (x y : Array Float) : Float × Array Float × Array Float := Id.run do
  let mut total : Float := 0
  let mut gx : Array Float := Array.replicate k 0
  let mut gy : Array Float := Array.replicate k 0
  for i in [0:k] do
    let mut L : Array Float := #[]
    let mut H : Array Float := #[]
    let mut covered := false
    let mut stop := false
    for j in [0:k] do
      if stop || j == i then continue
      let dx := x[j]! - x[i]!
      let dy := y[j]! - y[i]!
      let d := Float.sqrt (dx * dx + dy * dy)
      if d >= 2 then continue
      if d == 0 then
        if j < i then
          covered := true
          stop := true
        continue
      let phi := Float.atan2 dy dx
      let a := Float.acos (d / 2)
      let mut a0 := phi - a
      let mut b0 := phi + a
      while a0 < 0 do
        a0 := a0 + 2 * fpi
        b0 := b0 + 2 * fpi
      while a0 >= 2 * fpi do
        a0 := a0 - 2 * fpi
        b0 := b0 - 2 * fpi
      if b0 <= 2 * fpi then
        L := L.push a0
        H := H.push b0
      else
        L := L.push a0
        H := H.push (2 * fpi)
        L := L.push 0
        H := H.push (b0 - 2 * fpi)
    if covered then continue
    let (L', H') := sortArcs L H
    let q := L'.size
    let mut cur : Float := 0
    for s in [0:q+1] do
      let a0 := if s < q then L'[s]! else 2 * fpi
      if a0 > cur then
        let sa := Float.sin cur
        let sb := Float.sin a0
        let ca := Float.cos cur
        let cb := Float.cos a0
        total := total + 0.5 * ((a0 - cur) + x[i]! * (sb - sa) - y[i]! * (cb - ca))
        gx := gx.set! i (gx[i]! + (sb - sa))
        gy := gy.set! i (gy[i]! + (ca - cb))
      if s < q && H'[s]! > cur then cur := H'[s]!
  return (total, gx, gy)

/-! ## graphs (g table: 2g = 2p - n1 for connected graphs, p = minimum path cover) -/

def popcount (x : Nat) : Nat := Id.run do
  let mut c := 0
  let mut y := x
  while y > 0 do
    c := c + y % 2
    y := y / 2
  return c

def components (k : Nat) (adj : Array Nat) (mask : Nat) : Nat := Id.run do
  let mut seen := 0
  let mut cc := 0
  for v in [0:k] do
    if (mask >>> v) % 2 == 0 || (seen >>> v) % 2 == 1 then continue
    cc := cc + 1
    let mut fr := 1 <<< v
    seen := seen ||| fr
    let mut guard := 0
    while fr != 0 && guard < 64 do
      guard := guard + 1
      -- lowest set bit u
      let mut u := 0
      while (fr >>> u) % 2 == 0 do u := u + 1
      fr := fr &&& (fr - 1)
      let nb := adj[u]! &&& mask &&& (((1 <<< k) - 1) ^^^ seen)
      seen := seen ||| nb
      fr := fr ||| nb
  return cc

def minPathCover (k : Nat) (adj : Array Nat) : Nat := Id.run do
  let full := (1 <<< k) - 1
  let mut hp : Array Nat := Array.replicate (full + 1) 0
  for mask in [1:full+1] do
    if mask &&& (mask - 1) == 0 then
      hp := hp.set! mask mask
      continue
    let mut ends := 0
    for v in [0:k] do
      if (mask >>> v) % 2 == 1 then
        let rest := mask &&& (full ^^^ (1 <<< v))
        if hp[rest]! &&& adj[v]! != 0 then ends := ends ||| (1 <<< v)
    hp := hp.set! mask ends
  let mut pc : Array Nat := Array.replicate (full + 1) 0
  for mask in [1:full+1] do
    let low := mask &&& ((2 ^ 64 - mask) % 2 ^ 64)
    let mut best := 99
    let mut sub := mask
    while sub != 0 do
      if sub &&& low != 0 && hp[sub]! != 0 then
        let c := 1 + pc[mask &&& (full ^^^ sub)]!
        if c < best then best := c
      sub := (sub - 1) &&& mask
    pc := pc.set! mask best
  return pc[full]!

/-- `2g` of the graph with adjacency bitmasks `adj` (p - D form). -/
def g2Of (k : Nat) (adj : Array Nat) : Int :=
  let full := (1 <<< k) - 1
  if components k adj full != 1 then 0
  else
    let n1 := (List.range k).foldl (fun c i => if popcount adj[i]! == 1 then c + 1 else c) 0
    2 * (minPathCover k adj : Int) - n1

def pairsOf (k : Nat) : Array Nat × Array Nat := Id.run do
  let mut pi_ : Array Nat := #[]
  let mut pj_ : Array Nat := #[]
  for i in [0:k] do
    for j in [i+1:k] do
      pi_ := pi_.push i
      pj_ := pj_.push j
  return (pi_, pj_)

/-- `build_tables`: g2tab, gmin3, gmax3, pow3. -/
def buildTables (k : Nat) : Array Int × Array Int × Array Int × Array Nat := Id.run do
  let (pi_, pj_) := pairsOf k
  let npairs := pi_.size
  let ng := 1 <<< npairs
  let mut g2tab : Array Int := Array.replicate ng 0
  for e in [0:ng] do
    let mut adj : Array Nat := Array.replicate k 0
    for p in [0:npairs] do
      if (e >>> p) % 2 == 1 then
        adj := adj.set! pi_[p]! (adj[pi_[p]!]! ||| (1 <<< pj_[p]!))
        adj := adj.set! pj_[p]! (adj[pj_[p]!]! ||| (1 <<< pi_[p]!))
    g2tab := g2tab.set! e (g2Of k adj)
  let mut pow3 : Array Nat := Array.replicate (npairs + 1) 1
  for p in [1:npairs+1] do pow3 := pow3.set! p (pow3[p-1]! * 3)
  let n3 := pow3[npairs]!
  let mut gmin3 : Array Int := Array.replicate n3 0
  let mut gmax3 : Array Int := Array.replicate n3 0
  for idx in [0:n3] do
    let mut t := idx
    let mut e := 0
    let mut firstu : Int := -1
    for p in [0:npairs] do
      let st := t % 3
      t := t / 3
      if st == 1 then e := e ||| (1 <<< p)
      else if st == 2 && firstu < 0 then firstu := p
    if firstu < 0 then
      gmin3 := gmin3.set! idx g2tab[e]!
      gmax3 := gmax3.set! idx g2tab[e]!
      continue
    let fu := firstu.toNat
    let i0 := idx - 2 * pow3[fu]!
    let i1 := idx - pow3[fu]!
    gmin3 := gmin3.set! idx (min gmin3[i0]! gmin3[i1]!)
    gmax3 := gmax3.set! idx (max gmax3[i0]! gmax3[i1]!)
  return (g2tab, gmin3, gmax3, pow3)

/-! ## probabilities -/

def fminF (a b : Float) : Float := if a < b then a else b
def fmaxF (a b : Float) : Float := if a > b then a else b

/-- `cdf_diff`: P(X - Y <= z), X ~ U[a,b], Y ~ U[c,d] (float). -/
def cdfDiff (a b c d z : Float) : Float := Id.run do
  if b - a <= 0 && d - c <= 0 then return (if a - c <= z then 1.0 else 0.0)
  if b - a <= 0 then
    let t := (d - (a - z)) / (d - c)
    return (if t < 0 then 0 else if t > 1 then 1 else t)
  if d - c <= 0 then
    let t := (c + z - a) / (b - a)
    return (if t < 0 then 0 else if t > 1 then 1 else t)
  let mut pts : Array Float := #[a]
  let c1 := c + z
  let d1 := d + z
  if c1 > a && c1 < b then pts := pts.push c1
  if d1 > a && d1 < b then pts := pts.push d1
  pts := pts.push b
  if pts.size == 4 && pts[1]! > pts[2]! then
    let t := pts[1]!
    pts := (pts.set! 1 pts[2]!).set! 2 t
  let mut tot : Float := 0
  for s in [0:pts.size - 1] do
    let x0 := pts[s]!
    let x1 := pts[s+1]!
    let f0 := d - fminF (fmaxF (x0 - z) c) d
    let f1 := d - fminF (fmaxF (x1 - z) c) d
    tot := tot + 0.5 * (f0 + f1) * (x1 - x0)
  let p := tot / ((b - a) * (d - c))
  return (if p < 0 then 0 else if p > 1 then 1 else p)

def NSTRIP : Nat := 8

/-- `prob_unit`: staircase lower bounds (pin, pout) for P(|U_i - U_j| <= 1), P(> 1) (float). -/
def probUnit (xli xhi yli yhi xlj xhj ylj yhj : Float) : Float × Float := Id.run do
  let zx0 := xli - xhj
  let zx1 := xhi - xlj
  let mut inn : Float := 0
  let mut outer : Float := 0
  if zx1 <= zx0 then
    let ax := Float.abs zx0
    if ax < 1 then
      let t := Float.sqrt (1 - ax * ax)
      let mut p := cdfDiff yli yhi ylj yhj t - cdfDiff yli yhi ylj yhj (-t)
      if p < 0 then p := 0
      inn := p
      outer := p
    return (inn, 1 - outer)
  let mut F : Array Float := #[]
  for t in [0:NSTRIP+1] do
    F := F.push (cdfDiff xli xhi xlj xhj (zx0 + (zx1 - zx0) * t.toFloat / NSTRIP.toFloat))
  for t in [0:NSTRIP] do
    let x0 := zx0 + (zx1 - zx0) * t.toFloat / NSTRIP.toFloat
    let x1 := zx0 + (zx1 - zx0) * (t + 1).toFloat / NSTRIP.toFloat
    let px := F[t+1]! - F[t]!
    if px <= 0 then continue
    let amax := fmaxF (Float.abs x0) (Float.abs x1)
    let amin := if x0 <= 0 && x1 >= 0 then 0 else fminF (Float.abs x0) (Float.abs x1)
    if amax < 1 then
      let yt := Float.sqrt (1 - amax * amax)
      let p := cdfDiff yli yhi ylj yhj yt - cdfDiff yli yhi ylj yhj (-yt)
      if p > 0 then inn := inn + px * p
    if amin < 1 then
      let Yt := Float.sqrt (1 - amin * amin)
      let p := cdfDiff yli yhi ylj yhj Yt - cdfDiff yli yhi ylj yhj (-Yt)
      if p > 0 then outer := outer + px * p
  return (inn, if 1 - outer < 0 then 0 else 1 - outer)

/-! ## boxes -/

structure Acc where
  lb : Float := 0
  mid : Float := 0
  extra : Float := 0
  voldrop : Float := 0
  lossdrop : Float := 0
  l_int : Float := 0
  l_bnd : Float := 0
  l_str : Float := 0
  l_coi : Float := 0
  scored : Nat := 0
  dropped : Nat := 0
  visited : Nat := 0
  narb : Nat := 0       -- leaves with nonzero float value (the checker evaluates these)
  deriving Inhabited

def ivmin (al ah bl bh : Float) : Float :=
  if ah < bl then bl - ah else if bh < al then al - bh else 0
def ivmax (al ah bl bh : Float) : Float :=
  let t1 := Float.abs (ah - bl)
  let t2 := Float.abs (bh - al)
  if t1 > t2 then t1 else t2
def owner (d : Nat) : Nat := if d == 0 then 1 else (d + 3) / 2

/-- Kinds of scored leaves (for the exact evaluation). -/
inductive LeafKind | enl | straddle | normal
  deriving Inhabited, BEq

/-- What the float recursion decides for one box. -/
inductive Decision
  | drop                      -- outside the domain or gmax = 0 (contributes 0)
  | split (d : Nat)           -- bisect coordinate d
  | leaf (kind : LeafKind) (flt : Float)   -- scored leaf with float value flt
  deriving Inhabited

/-- The body of `process` for one box: the decision, plus the float accumulator update for leaves. -/
def decide (C : Ctx) (lo hi : Array Float) (acc : Acc) : Decision × Acc := Id.run do
  let k := C.k
  let m := C.m
  let mut acc := { acc with visited := acc.visited + 1 }
  let mut xl : Array Float := Array.replicate k 0
  let mut xh : Array Float := Array.replicate k 0
  let mut yl : Array Float := Array.replicate k 0
  let mut yh : Array Float := Array.replicate k 0
  xl := xl.set! 1 lo[0]!; xh := xh.set! 1 hi[0]!
  for j in [2:k] do
    xl := xl.set! j lo[2*j-3]!; xh := xh.set! j hi[2*j-3]!
    yl := yl.set! j lo[2*j-2]!; yh := yh.set! j hi[2*j-2]!
  -- symmetry order
  let mut straddle := 0
  let mut sdim := 0
  let mut spair := 0
  let mut swid : Float := 0
  for j in [2:k-1] do
    if xl[j]! > xh[j+1]! then return (.drop, acc)
    if xh[j]! > xl[j+1]! then
      straddle := straddle + 1
      spair := j
      let w1 := xh[j]! - xl[j]!
      let w2 := xh[j+1]! - xl[j+1]!
      if w1 > swid then
        swid := w1
        sdim := 2 * j - 3
      if w2 > swid then
        swid := w2
        sdim := 2 * (j + 1) - 3
  let mut pres := 0
  let mut und := 0
  let mut involved := 0
  let mut dmn : Array Float := Array.replicate C.npairs 0
  let mut dmx : Array Float := Array.replicate C.npairs 0
  let mut idx3 := 0
  for p in [0:C.npairs] do
    let i := C.pi_[p]!
    let j := C.pj_[p]!
    let dxm := ivmin xl[i]! xh[i]! xl[j]! xh[j]!
    let dym := ivmin yl[i]! yh[i]! yl[j]! yh[j]!
    let dxM := ivmax xl[i]! xh[i]! xl[j]! xh[j]!
    let dyM := ivmax yl[i]! yh[i]! yl[j]! yh[j]!
    let dmin2 := dxm * dxm + dym * dym
    let dmax2 := dxM * dxM + dyM * dyM
    dmn := dmn.set! p (Float.sqrt dmin2)
    dmx := dmx.set! p (Float.sqrt dmax2)
    if dmax2 <= 1 then
      pres := pres ||| (1 <<< p)
      idx3 := idx3 + C.pow3[p]!
    else if dmin2 <= 1 then
      und := und ||| (1 <<< p)
      idx3 := idx3 + 2 * C.pow3[p]!
      involved := involved ||| (1 <<< i) ||| (1 <<< j)
  let gmin := C.gmin3[idx3]!
  let gmax := C.gmax3[idx3]!
  if gmax <= 0 then return (.drop, acc)
  let mut width : Float := 0
  let mut rwidth : Float := 0
  let mut dw := 0
  let mut drw := 0
  for d in [0:m] do
    let w := hi[d]! - lo[d]!
    if w > width then
      width := w
      dw := d
    if (involved >>> owner d) % 2 == 1 && w > rwidth then
      rwidth := w
      drw := d
  let mut v : Float := 1
  for d in [0:m] do v := v * (hi[d]! - lo[d]!)
  if width > C.W0 then return (.split dw, acc)
  let mut xc : Array Float := Array.replicate k 0
  let mut yc : Array Float := Array.replicate k 0
  let mut del : Array Float := Array.replicate k 0
  let mut hw : Array Float := Array.replicate m 0
  for i in [0:k] do
    xc := xc.set! i (0.5 * (xl[i]! + xh[i]!))
    yc := yc.set! i (0.5 * (yl[i]! + yh[i]!))
    let a := xh[i]! - xl[i]!
    let b := yh[i]! - yl[i]!
    del := del.set! i (0.5 * Float.sqrt (a * a + b * b))   -- hypot(a, b): exact sum of squares here
  for d in [0:m] do hw := hw.set! d (hi[d]! - lo[d]!)
  let mut m1 : Array Float := Array.replicate k 0
  let mut m2 : Array Float := Array.replicate k 0
  let mut m4 : Array Float := Array.replicate k 0
  for i in [0:k] do
    let a := 0.5 * (xh[i]! - xl[i]!)
    let bb := 0.5 * (yh[i]! - yl[i]!)
    m2 := m2.set! i ((a * a + bb * bb) / 3)
    m1 := m1.set! i (Float.sqrt m2[i]!)
    m4 := m4.set! i (a * a * a * a / 5 + 2 * (a * a / 3) * (bb * bb / 3) + bb * bb * bb * bb / 5)
  let mut Rmax : Float := 0
  let mut Er : Float := 0
  let mut sqrtEr2 : Float := 0
  let mut coincident := false
  for p in [0:C.npairs] do
    if coincident then continue
    if dmn[p]! >= 2 then continue
    if dmn[p]! <= 0 then
      coincident := true
      continue
    let i := C.pi_[p]!
    let j := C.pj_[p]!
    let dd := if dmx[p]! < 2 then dmx[p]! else 2
    let dl := del[i]! + del[j]!
    let mut cr : Float := 0
    let mut c0 : Float := 0
    if dmx[p]! < 1.98 then
      let hmin := 0.5 * Float.sqrt (4 - dmx[p]! * dmx[p]!)
      cr := 1 / (2 * hmin)
      c0 := 0
    else
      cr := 0
      c0 := 2 * (Float.asin (dd / 2) - Float.asin (dmn[p]! / 2))
    let tanmax := if dl / dmn[p]! < fpi then dl / dmn[p]! else fpi
    let motion := cr * dl + c0 + tanmax
    let ex := xc[j]! - xc[i]!
    let ey := yc[j]! - yc[i]!
    let dc := Float.sqrt (ex * ex + ey * ey)
    let mut nv : Nat := 2
    if dc < 2 && dc > 0 then
      let hh := Float.sqrt (1 - dc * dc / 4)
      let ux := ex / dc
      let uy := ey / dc
      nv := 0
      for sgnI in [0:2] do
        let sgn : Float := if sgnI == 0 then -1 else 1
        let px := xc[i]! + 0.5 * dc * ux - sgn * hh * uy
        let py := yc[i]! + 0.5 * dc * uy + sgn * hh * ux
        let pmove := del[i]! + motion
        let mut cov := false
        for q in [0:k] do
          if cov || q == i || q == j then continue
          let qx := px - xc[q]!
          let qy := py - yc[q]!
          if Float.sqrt (qx * qx + qy * qy) + pmove + del[q]! < 1 then cov := true
        if !cov then nv := nv + 1
    if nv == 0 then continue
    let S2 := m2[i]! + m2[j]! + 2 * m1[i]! * m1[j]!
    let S1 := m1[i]! + m1[j]!
    let S4 := 8 * (m4[i]! + m4[j]!)
    let d2 := dmn[p]! * dmn[p]!
    let Etan := if S2 / dmn[p]! < fpi * S1 then S2 / dmn[p]! else fpi * S1
    let Etan2 := if S4 / d2 < fpi * fpi * S2 then S4 / d2 else fpi * fpi * S2
    let nvf := nv.toFloat
    Rmax := Rmax + nvf * dl * motion
    Er := Er + nvf * (cr * S2 + c0 * S1 + Etan)
    sqrtEr2 := sqrtEr2 + nvf * Float.sqrt (3 * (cr * cr * S4 + c0 * c0 * S2 + Etan2))
  let gminF := Float.ofInt gmin
  let gmaxF := Float.ofInt gmax
  if coincident then
    let mut delta : Float := 0
    for i in [0:k] do if del[i]! > delta then delta := del[i]!
    let mut xs : Array Float := Array.replicate k 0
    let mut ys : Array Float := Array.replicate k 0
    for i in [0:k] do
      xs := xs.set! i (xc[i]! / (1 + delta))
      ys := ys.set! i (yc[i]! / (1 + delta))
    let Aenl := (1 + delta) * (1 + delta) * (unionAreaGrad k xs ys).1
    let Ac := (unionAreaGrad k xc yc).1
    let c := if gmin > 0 && straddle == 0 then v * 0.5 * gminF * lo[0]! * Float.pow Aenl (-C.sexp) else 0
    let est := C.PREF * v * 0.5 * gmaxF * 0.5 * (lo[0]! + hi[0]!) * Float.pow Ac (-C.sexp) - C.PREF * c
    if est > C.EPS && width > C.WF then return (.split dw, acc)
    acc := { acc with lb := acc.lb + c, extra := acc.extra + c, scored := acc.scored + 1, l_coi := acc.l_coi + est }
    if c == 0 then acc := { acc with voldrop := acc.voldrop + v, dropped := acc.dropped + 1 }
    else acc := { acc with narb := acc.narb + 1 }
    return (.leaf .enl c, acc)
  let (A, gx, gy) := unionAreaGrad k xc yc
  let mut bv : Array Float := Array.replicate m 0
  bv := bv.set! 0 gx[1]!
  for j in [2:k] do
    bv := bv.set! (2*j-3) gx[j]!
    bv := bv.set! (2*j-2) gy[j]!
  let mut sumb : Float := 0
  let mut sumb2 : Float := 0
  for d in [0:m] do
    sumb := sumb + Float.abs bv[d]! * hw[d]! / 2
    sumb2 := sumb2 + bv[d]! * bv[d]! * hw[d]! * hw[d]! / 12
  let ap := A + Er
  let tmin := A - sumb
  let r2c := 0.5 * (lo[0]! + hi[0]!)
  let s := C.sexp
  let mut val : Float := 0
  if tmin > 0 then
    let t2 := Float.sqrt sumb2 + sqrtEr2
    let h0 : Float := hw[0]!
    let b0 : Float := bv[0]!
    let pA1 : Float := Float.pow A (-s - 1)
    let term1 : Float := r2c * Float.pow ap (-s)
    let term2 : Float := s * pA1 * (b0 * h0 * h0 / (12 : Float))
    let term3 : Float := s * pA1 * (h0 / (2 : Float)) * Er
    let term4 : Float := (h0 / (4 : Float)) * s * (s + 1) * Float.pow tmin (-s - 2) * t2 * t2
    val := term1 - term2 - term3 - term4
    if val < 0 then val := 0
  let mid := r2c * Float.pow A (-s)
  let mut Alow := A - sumb - Rmax
  if Alow < fpi then Alow := fpi
  let pot := C.PREF * v * 0.5 * gmaxF * hi[0]! * Float.pow Alow (-s)
  let fmin_pt := lo[0]! * Float.pow (A + sumb + Rmax) (-s)
  let fmax_pt := hi[0]! * Float.pow Alow (-s)
  let EV := fun (q : Float) =>
    if q * fmin_pt > val - (1 - q) * fmax_pt then q * fmin_pt else val - (1 - q) * fmax_pt
  if straddle > 0 then
    let mut c : Float := 0
    if straddle == 1 && gmin > 0 then
      let j := spair
      let pord := cdfDiff xl[j]! xh[j]! xl[j+1]! xh[j+1]! 0.0
      let c1 := v * 0.5 * gminF * fmin_pt * pord
      let c2 := v * 0.5 * gminF * (val - (1 - pord) * fmax_pt)
      c := if c1 > c2 then c1 else c2
    let est := C.PREF * v * 0.5 * gmaxF * mid - C.PREF * c
    if est > C.EPS && swid > C.WF then return (.split sdim, acc)
    acc := { acc with lb := acc.lb + c, extra := acc.extra + c, scored := acc.scored + 1,
                      lossdrop := acc.lossdrop + (pot - C.PREF * c), l_str := acc.l_str + est }
    if c == 0 then acc := { acc with voldrop := acc.voldrop + v, dropped := acc.dropped + 1 }
    else acc := { acc with narb := acc.narb + 1 }
    return (.leaf .straddle c, acc)
  let lbx := if gmin > 0 then v * 0.5 * gminF * val else 0
  let mut extra : Float := 0
  if gmin < gmax then
    let mut best : Float := 0
    let mut pin_ : Array Float := #[]
    let mut pout_ : Array Float := #[]
    let mut up : Array Nat := #[]
    for p in [0:C.npairs] do
      if (und >>> p) % 2 == 0 then continue
      let i := C.pi_[p]!
      let j := C.pj_[p]!
      let (pin, pout) := probUnit xl[i]! xh[i]! yl[i]! yh[i]! xl[j]! xh[j]! yl[j]! yh[j]!
      pin_ := pin_.push pin
      pout_ := pout_.push pout
      up := up.push p
      let gp := C.gmin3[idx3 - C.pow3[p]!]!
      let ga := C.gmin3[idx3 - 2 * C.pow3[p]!]!
      let sc := Float.ofInt (gp - gmin) * EV pin + Float.ofInt (ga - gmin) * EV pout
      if sc > best then best := sc
    let nu := up.size
    for t1 in [0:nu] do
      for t2 in [t1+1:nu] do
        let p1 := up[t1]!
        let p2 := up[t2]!
        let disjoint := C.pi_[p1]! != C.pi_[p2]! && C.pi_[p1]! != C.pj_[p2]! &&
          C.pj_[p1]! != C.pi_[p2]! && C.pj_[p1]! != C.pj_[p2]!
        let mut sc : Float := 0
        for s1 in [0:2] do
          for s2 in [0:2] do
            let id := idx3 - (if s1 == 1 then C.pow3[p1]! else 2 * C.pow3[p1]!)
              - (if s2 == 1 then C.pow3[p2]! else 2 * C.pow3[p2]!)
            let gs := C.gmin3[id]!
            if gs <= gmin then continue
            let q1 := if s1 == 1 then pin_[t1]! else pout_[t1]!
            let q2 := if s2 == 1 then pin_[t2]! else pout_[t2]!
            let pl := if disjoint then q1 * q2 else (if q1 + q2 - 1 > 0 then q1 + q2 - 1 else 0)
            sc := sc + EV pl * Float.ofInt (gs - gmin)
        if sc > best then best := sc
    extra := v * 0.5 * best
    let est := C.PREF * v * 0.5 * gmaxF * mid - C.PREF * (lbx + extra)
    if est > C.EPS && rwidth > C.WF then return (.split drw, acc)
    acc := { acc with lossdrop := acc.lossdrop + (pot - C.PREF * (lbx + extra)), l_bnd := acc.l_bnd + est }
  else
    let loss := C.PREF * v * 0.5 * gminF * (mid - val)
    if loss > C.EPS && width > C.WF then return (.split dw, acc)
    acc := { acc with l_int := acc.l_int + loss }
  acc := { acc with lb := acc.lb + (lbx + extra), extra := acc.extra + extra,
                    mid := acc.mid + v * 0.5 * gminF * mid, scored := acc.scored + 1 }
  if gmin <= 0 then acc := { acc with dropped := acc.dropped + 1 }
  if lbx + extra != 0 then acc := { acc with narb := acc.narb + 1 }
  return (.leaf .normal (lbx + extra), acc)

/-- `process` with fuel (float only). -/
def process (C : Ctx) : Nat → Array Float → Array Float → Acc → Acc
  | 0, _, _, acc => acc
  | fuel + 1, lo, hi, acc =>
    match decide C lo hi acc with
    | (.split d, acc) =>
      let mid := 0.5 * (lo[d]! + hi[d]!)
      let acc := process C fuel lo (hi.set! d mid) acc
      process C fuel (lo.set! d mid) hi acc
    | (_, acc) => acc

/-- `initial_boxes`: split the root breadth first at the widest coordinate into at least n boxes. -/
def initialBoxes (m : Nat) (lo hi : Array Float) (n : Nat) : Array (Array Float × Array Float) := Id.run do
  let mut arr : Array (Array Float × Array Float) := #[(lo, hi)]
  let mut guard := 0
  while arr.size < n && guard < 64 do
    guard := guard + 1
    let mut nb : Array (Array Float × Array Float) := #[]
    for (l, h) in arr do
      let mut dw := 0
      let mut w : Float := -1
      for d in [0:m] do
        if h[d]! - l[d]! > w then
          w := h[d]! - l[d]!
          dw := d
      let mid := 0.5 * (l[dw]! + h[dw]!)
      nb := nb.push (l, h.set! dw mid)
      nb := nb.push (l.set! dw mid, h)
    arr := nb
  return arr

def rootBox (k : Nat) : Array Float × Array Float := Id.run do
  let m := 2 * k - 3
  let Rd := (k - 2).toFloat
  let mut lo : Array Float := Array.replicate m 0
  let mut hi : Array Float := Array.replicate m 0
  lo := lo.set! 0 0; hi := hi.set! 0 Rd
  for j in [2:k] do
    lo := lo.set! (2*j-3) (-Rd); hi := hi.set! (2*j-3) Rd
    lo := lo.set! (2*j-2) (if j == 2 then 0 else -Rd); hi := hi.set! (2*j-2) Rd
  return (lo, hi)

def mkCtx (k : Nat) (W0 WF EPS PREF : Float) : Ctx :=
  let (pi_, pj_) := pairsOf k
  let (_, gmin3, gmax3, pow3) := buildTables k
  { k := k, m := 2 * k - 3, npairs := pi_.size, pi_ := pi_, pj_ := pj_, W0 := W0, WF := WF, EPS := EPS,
    sexp := k.toFloat - 0.5, PREF := PREF, gmin3 := gmin3, gmax3 := gmax3, pow3 := pow3 }

end BHH.Cert.Flt
