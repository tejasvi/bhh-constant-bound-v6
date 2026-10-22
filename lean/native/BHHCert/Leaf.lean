/-
The rigorous leaf bound (core Lean only; kernel-friendly).  For a box `Q` (exact dyadic corners) it returns
an integer `L` with `L / 2^OS ≤ ∫_{Q ∩ D_k} r_2 · 2g(G_1(y)) · φ(A(y)) dx` (proved in BHH/Leaf*.lean from the
box lemmas and the hypotheses `GreenFormula`, `VertexLemma`).  The case split follows the paper (and the
checker chk_ck14): coinciding points possible (Prop. 3.8), straddling boxes (Prop. 3.7), boxes with
undetermined edges (Prop. 3.6), interior boxes (Prop. 3.4 and the second bracket).
-/
import BHHCert.Union

namespace BHH.Cert

/-- Output scale: leaf values are integers at scale `2^-OS`. -/
def OS : Nat := 256

/-- Source of candidate values for `arcsin` (never trusted). -/
abbrev AsinFn := Int → Int

/-- The g table (2g values): `gmin idx ≤ 2g(e)` for every completion `e` of the edge state `idx` (base 3:
digit 0 absent, 1 present, 2 undetermined) is the only property used (`gmax` only steers which bounds are
computed). -/
structure GTab where
  gmin : Nat → Int
  gmax : Nat → Int

/-! ## small helpers -/

def listGet (l : List Int) (i : Nat) : Int := l.getD i 0

/-- least distance between `[a, b]` and `[c, d]` -/
def gapI (a b c d : Int) : Int := Max.max (Max.max (c - b) (a - d)) 0
/-- largest distance between `[a, b]` and `[c, d]` -/
def spanI (a b c d : Int) : Int := Max.max (d - a).natAbs (b - c).natAbs

/-- Per-point rectangle data (fixed point, exact). -/
structure PtBox where
  xl : Int
  xh : Int
  yl : Int
  yh : Int
  deriving Inhabited

def PtBox.xc (p : PtBox) : Int := (p.xl + p.xh) / 2
def PtBox.yc (p : PtBox) : Int := (p.yl + p.yh) / 2
/-- half-widths -/
def PtBox.ha (p : PtBox) : Int := (p.xh - p.xl) / 2
def PtBox.hb (p : PtBox) : Int := (p.yh - p.yl) / 2

/-- The rectangles `R_0 = {0}`, `R_1 = [lo_0, hi_0] × {0}`, `R_j` (coordinates `2j-3`, `2j-2`). -/
def ptBoxes (k : Nat) (lo hi : List Int) : List PtBox :=
  (List.range k).map fun j =>
    if j == 0 then ⟨0, 0, 0, 0⟩
    else if j == 1 then ⟨listGet lo 0, listGet hi 0, 0, 0⟩
    else ⟨listGet lo (2 * j - 3), listGet hi (2 * j - 3), listGet lo (2 * j - 2), listGet hi (2 * j - 2)⟩

/-- The pairs `(i, j)`, `i < j`, in lexicographic order. -/
def pairList (k : Nat) : List (Nat × Nat) :=
  (List.range k).foldr (fun i acc => ((List.range k).filter (fun j => i < j)).map (fun j => (i, j)) ++ acc) []

/-- exact `(d^-)^2`, `(d^+)^2` at scale `2^-2PR` -/
def d2minmax (P Q : PtBox) : Int × Int :=
  let gx := gapI P.xl P.xh Q.xl Q.xh
  let gy := gapI P.yl P.yh Q.yl Q.yh
  let sx := spanI P.xl P.xh Q.xl Q.xh
  let sy := spanI P.yl P.yh Q.yl Q.yh
  (gx * gx + gy * gy, sx * sx + sy * sy)

def pow3 (n : Nat) : Nat := 3 ^ n

/-! ## φ(t) = t^{-s}, s = k - 1/2 -/

/-- `φ`, `φ'`, `φ''` at an exact point `t` (fixed point), as intervals; `none` unless `t ≥ 2^-16` and the
enclosure of `t^k` is positive. -/
def phiAt (k : Nat) (t : Int) : Option (Iv × Iv × Iv) :=
  if t < 2 ^ (PR - 16) then none else
  let ti := Iv.pt t
  let tk := (List.range k).foldl (fun acc _ => Iv.mul acc ti) (Iv.int 1)
  if tk.lo ≤ 0 then none else
  let f0 := Iv.div (Iv.sqrt ti) tk
  let s2 : Nat := 2 * k - 1                 -- 2s
  let f1 := Iv.neg (Iv.divNat (Iv.mulNat (Iv.div f0 ti) s2) 2)
  let f2 := Iv.divNat (Iv.mulNat (Iv.div (Iv.div f0 ti) ti) (s2 * (s2 + 2))) 4
  some (f0, f1, f2)

/-! ## arcsin by monotone verification -/

/-- An upper bound of `arcsin x` for `0 ≤ x < 1` (`x` fixed point), from a candidate checked with `sin`;
`π/2` if the check fails. -/
def asinHi (cs : Int → Iv × Iv) (cand : AsinFn) (x : Int) : Int :=
  let halfPi := shrU piHi 1
  let a := cand x + 2 ^ (PR - 40)
  if 0 ≤ a ∧ 2 * a ≤ piLo then
    if x ≤ (cs a).2.lo then a else halfPi
  else halfPi

/-- A lower bound of `arcsin x` for `0 ≤ x ≤ 1`; `0` if the check fails. -/
def asinLo (cs : Int → Iv × Iv) (cand : AsinFn) (x : Int) : Int :=
  let a := cand x - 2 ^ (PR - 40)
  if 0 ≤ a ∧ 2 * a ≤ piLo then
    if (cs a).2.hi ≤ x then a else 0
  else 0

/-! ## the vertex remainder (Lemma 3.1, Remark 3.2, Lemma 3.3) -/

structure RemRes where
  Rmax : Int    -- ≥ max_Q ϱ
  Er : Int      -- ≥ E ϱ
  sEr2 : Int    -- ≥ (E ϱ²)^{1/2}
  deriving Inhabited

/-- second moments etc. of a point uniform on its rectangle (half-sides `a`, `b`) -/
def moments (P : PtBox) : Iv × Iv × Iv × Iv :=
  let a := Iv.pt P.ha
  let b := Iv.pt P.hb
  let a2 := Iv.sqr a
  let b2 := Iv.sqr b
  let del := Iv.sqrt (Iv.add a2 b2)
  let m2 := Iv.divNat (Iv.add a2 b2) 3
  let m1 := Iv.sqrt m2
  let m4 := Iv.add (Iv.add (Iv.divNat (Iv.sqr a2) 5) (Iv.divNat (Iv.mulNat (Iv.mul a2 b2) 2) 9))
    (Iv.divNat (Iv.sqr b2) 5)
  (del, m1, m2, m4)

/-- `1.98² = 3.9204` at scale `2^-2PR`: the first choice of `(λ, μ)` is used when `(d^+)^2 < 3.9204`. -/
def thr198 : Int := (39204 * ONE * ONE) / 10000

/-- Remark 3.2 for one vertex `(px, py)` of the pair `(i, j)`: certified covered by the disk of some third point `l`
(`|P - c_l| < 1 - (ε_i + motion + ε_l)`, all upper bounds). -/
def vertexCovered (bx : List PtBox) (mom : List (Iv × Iv × Iv × Iv)) (i j : Nat) (deli : Iv) (motion : Int)
    (px py : Iv) : Bool :=
  ((List.range bx.length).filter (fun l => l != i && l != j)).any fun l =>
    let Pl := bx.getD l default
    let dell := (mom.getD l default).1
    let R0 := ONE - (deli.hi + motion + dell.hi)
    if R0 ≤ 0 then false
    else
      let dx := Iv.sub px (Iv.pt Pl.xc)
      let dy := Iv.sub py (Iv.pt Pl.yc)
      let dist2 := Iv.add (Iv.sqr dx) (Iv.sqr dy)
      dist2.hi < shrD (R0 * R0) PR

/-- `ν`: the number of vertices of the pair `(i, j)` (at the centre configuration) not certified covered; 2 when the
circles around the centres do not certainly meet in two points -/
def nvCount (bx : List PtBox) (mom : List (Iv × Iv × Iv × Iv)) (i j : Nat) (deli : Iv) (motion : Int) : Nat :=
  let four2 : Int := 4 * ONE * ONE
  let Pi := bx.getD i default
  let Pj := bx.getD j default
  let wx := Pj.xc - Pi.xc
  let wy := Pj.yc - Pi.yc
  let dc2 := wx * wx + wy * wy                         -- scale 2^-2PR
  let dc2I := Iv.div2e (Iv.pt dc2) PR
  if 0 < dc2 ∧ dc2 < four2 ∧ 0 < dc2I.lo then
    -- s = sqrt(1/dc² - 1/4)
    let inv2 := Iv.div (Iv.int 1) dc2I
    let sIv := Iv.sqrt (Iv.sub inv2 (Iv.div2e (Iv.int 1) 2))
    let mx := Iv.add (Iv.pt Pi.xc) (Iv.div2e (Iv.pt wx) 1)
    let my := Iv.add (Iv.pt Pi.yc) (Iv.div2e (Iv.pt wy) 1)
    let ox := Iv.mul sIv (Iv.pt (-wy))
    let oy := Iv.mul sIv (Iv.pt wx)
    (if vertexCovered bx mom i j deli motion (Iv.add mx ox) (Iv.add my oy) then 0 else 1) +
    (if vertexCovered bx mom i j deli motion (Iv.sub mx ox) (Iv.sub my oy) then 0 else 1)
  else 2

/-- The contribution of the pair `(i, j)` to `(R_max, E ϱ, (E ϱ²)^{1/2})`: `none` on failure, else `(ν, a, b, c)`
meaning `ν a`, `ν b`, `ν c` (`ν = 0` and zeros when the pair has `d^- ≥ 2`). -/
def remPair (cs : Int → Iv × Iv) (asinC : AsinFn) (bx : List PtBox) (mom : List (Iv × Iv × Iv × Iv))
    (i j : Nat) (d2mn d2mx : Int) : Option (Nat × Int × Int × Int) :=
  let four2 : Int := 4 * ONE * ONE
  if four2 ≤ d2mn then some (0, 0, 0, 0)
  else if d2mn ≤ 0 then none
  else
    let (deli, m1i, m2i, m4i) := mom.getD i default
    let (delj, m1j, m2j, m4j) := mom.getD j default
    let d2mnI := Iv.div2e (Iv.pt d2mn) PR                 -- d2mn is at scale 2^-2PR
    let dmn := Iv.sqrt d2mnI
    let q4 := Iv.sqrt (Iv.div2e (Iv.pt (four2 - d2mx)) PR)
    let first := d2mx < thr198
    if dmn.lo ≤ 0 ∨ d2mnI.lo ≤ 0 ∨ (first ∧ q4.lo ≤ 0) then none else
    let dl := Iv.add deli delj
    let c1 : Int := if first then (Iv.inv q4).hi else 0
    let c0 : Int := if first then 0 else
      let up := if d2mx < four2 then asinHi cs asinC (shrU (Iv.sqrt (Iv.div2e (Iv.pt d2mx) PR)).hi 1)
                else shrU piHi 1
      let lw := asinLo cs asinC (shrD dmn.lo 1)
      2 * (up - lw)
    let tcap : Int := Min.min (Iv.div dl dmn).hi piHi
    let motion : Int := shrU (c1 * dl.hi) PR + c0 + tcap
    let nv := nvCount bx mom i j deli motion
    if nv == 0 then some (0, 0, 0, 0)
    else
      let S1 := Iv.add m1i m1j
      let S2 := Iv.add (Iv.add m2i m2j) (Iv.mulNat (Iv.mul m1i m1j) 2)
      let S4 := Iv.mulNat (Iv.add m4i m4j) 8
      let Et : Int := Min.min (Iv.div S2 dmn).hi (Iv.mul piIv S1).hi
      let Et2 : Int := Min.min (Iv.div S4 d2mnI).hi (Iv.mul (Iv.sqr piIv) S2).hi
      let rmax := shrU (dl.hi * motion) PR
      let er := shrU (c1 * S2.hi) PR + shrU (c0 * S1.hi) PR + Et
      let t := shrU (c1 * c1) PR
      let inner := shrU (t * S4.hi) PR + shrU (shrU (c0 * c0) PR * S2.hi) PR + Et2
      let ser2 := (Iv.sqrt (Iv.pt (3 * inner))).hi
      some (nv, rmax, er, ser2)

/-- Remainder bounds (sums over the pairs); `none` if some pair fails. -/
def remainder (cs : Int → Iv × Iv) (asinC : AsinFn) (bx : List PtBox) (pairs : List (Nat × Nat))
    (d2s : List (Int × Int)) : Option RemRes :=
  let mom := bx.map moments
  (pairs.zip d2s).foldl (fun acc pd =>
    match acc, remPair cs asinC bx mom pd.1.1 pd.1.2 pd.2.1 pd.2.2 with
    | some r, some (nv, a, b, c) => some ⟨r.Rmax + nv * a, r.Er + nv * b, r.sEr2 + nv * c⟩
    | _, _ => none) (some ⟨0, 0, 0⟩)

/-! ## probabilities -/

/-- Enclosure of `F(z) = P(X - Y ≤ z)`, `X ~ U[a, b]`, `Y ~ U[c, d]` (fixed point; exact inputs). -/
def cdfIv (a b c d z : Int) : Iv :=
  let w1 := b - a
  let w2 := d - c
  if w1 == 0 ∧ w2 == 0 then (if a - c ≤ z then Iv.int 1 else Iv.int 0)
  else if w1 == 0 ∨ w2 == 0 then
    let t := (if w1 == 0 then d - a else c - a) + z
    let w := if w1 == 0 then w2 else w1
    if t ≤ 0 then Iv.int 0 else if w ≤ t then Iv.int 1 else Iv.div (Iv.pt t) (Iv.pt w)
  else
    let p := Min.min w1 w2
    let q := Max.max w1 w2
    let u := d - a + z
    if u ≤ 0 then Iv.int 0
    else if p + q ≤ u then Iv.int 1
    else if p ≤ 0 then ⟨0, ONE⟩
    else
      let den := Iv.mulNat (Iv.mul (Iv.pt p) (Iv.pt q)) 2
      if den.lo ≤ 0 then ⟨0, ONE⟩
      else if u ≤ p then Iv.div (Iv.sqr (Iv.pt u)) den
      else if u ≤ q then Iv.div (Iv.pt (2 * u - p)) (Iv.pt (2 * q))
      else Iv.sub (Iv.int 1) (Iv.div (Iv.sqr (Iv.pt (p + q - u))) den)

/-- Lower bounds `(pin, pout)` for `P(|U_i - U_j| ≤ 1)` and `P(|U_i - U_j| > 1)` (8 strips). -/
def probStrips (P Q : PtBox) : Int × Int :=
  let zx0 := P.xl - Q.xh
  let wz := (P.xh - Q.xl) - zx0
  let ydeg := P.yh == P.yl ∧ Q.yh == Q.yl
  if wz ≤ 0 then (0, 0)
  else
    let xt := (List.range 9).map fun (t : Nat) => zx0 + (wz * (t : Int)) / 8
    let F := xt.map fun z => cdfIv P.xl P.xh Q.xl Q.xh z
    let strips := (List.range 8).map fun t => (xt.getD t 0, xt.getD (t + 1) 0, F.getD t default, F.getD (t + 1) default)
    let (pin, outer) := strips.foldl (fun (pin, outer) (x0, x1, F0, F1) =>
      let px := Iv.sub F1 F0
      let amax := Max.max x0.natAbs x1.natAbs
      let amin : Nat := if x0 ≤ 0 ∧ 0 ≤ x1 then 0 else Min.min x0.natAbs x1.natAbs
      let pin' :=
        if (amax : Int) < ONE then
          let yb := (Iv.sqrt (Iv.sub (Iv.int 1) (Iv.sqr (Iv.pt amax)))).lo
          if 0 < yb then
            let G := Iv.sub (cdfIv P.yl P.yh Q.yl Q.yh yb) (cdfIv P.yl P.yh Q.yl Q.yh (-yb))
            Iv.add pin (Iv.mul G px)
          else pin
        else pin
      let outer' :=
        if (amin : Int) < ONE then
          let yb := (Iv.sqrt (Iv.sub (Iv.int 1) (Iv.sqr (Iv.pt amin)))).hi
          let G := if ydeg then (if (P.yl - Q.yl).natAbs ≤ yb.toNat then Iv.int 1 else Iv.int 0)
                   else Iv.sub (cdfIv P.yl P.yh Q.yl Q.yh yb) (cdfIv P.yl P.yh Q.yl Q.yh (-yb))
          Iv.add outer (Iv.mul G px)
        else outer
      (pin', outer')) (Iv.int 0, Iv.int 0)
    (Max.max pin.lo 0, Max.max (ONE - outer.hi) 0)

/-- `EV(q) = max(q fmin, val - (1 - q) fmax)`, clipped at 0 (lower bounds `q, fmin, val`, upper `fmax`). -/
def evLB (q fmin fmax val : Int) : Int :=
  let a := shrD (q * fmin) PR
  let b := val - shrU ((ONE - q) * fmax) PR
  Max.max (Max.max a b) 0

/-! ## the leaf -/

/-- Result of a leaf evaluation, for diagnostics: the value and a reason code. -/
structure LeafOut where
  val : Int       -- lower bound at scale 2^-OS (2g units)
  code : Nat      -- 0 ok, 1 outside, 2 enl-zero, 3 union failed, 4 remainder failed, 5 nothing to do
  deriving Inhabited

/-- the rigorous leaf bound -/
def leafLB (k : Nat) (gt : GTab) (cs : Int → Iv × Iv) (cand : CandFn) (asinC : AsinFn)
    (lo hi : List Int) : LeafOut :=
  let m := 2 * k - 3
  let bx := ptBoxes k lo hi
  let pairs := pairList k
  let d2s := pairs.map fun (i, j) => d2minmax (bx.getD i default) (bx.getD j default)
  let one2 : Int := ONE * ONE
  -- edge states and the base-3 index
  let st : List Nat := d2s.map fun (mn, mx) => if mx ≤ one2 then 1 else if one2 < mn then 0 else 2
  let idx3 : Nat := (st.zip (List.range st.length)).foldl (fun acc (s, p) => acc + s * pow3 p) 0
  let gmin := gt.gmin idx3
  let gmax := gt.gmax idx3
  -- domain: r2 >= 0, eta_2 >= 0, xi order
  let x (j : Nat) := (bx.getD j default)
  let ordPairs := (List.range k).filter (fun j => 2 ≤ j ∧ j + 1 < k)
  let outside0 := listGet lo 0 < 0 ∨ (2 < k ∧ (x 2).yl < 0)
  let outside := outside0 ∨ ordPairs.any (fun j => (x j).xl > (x (j + 1)).xh)
  let strad := ordPairs.filter (fun j => (x j).xh > (x (j + 1)).xl)
  let nstr := strad.length
  -- volume (exact, scale 2^-(m PR))
  let vnum : Int := (List.range m).foldl (fun acc d => acc * (listGet hi d - listGet lo d)) 1
  let finish (lb : Int) : Int := shrD (vnum * lb) (m * PR + PR - OS)
  let lo0 := listGet lo 0
  let hi0 := listGet hi 0
  if outside then ⟨0, 1⟩ else
  -- Prop. 3.8: some pair with d^- = 0
  if d2s.any (fun (mn, _) => mn == 0) then
    if ¬(nstr == 0 ∧ 0 < gmin ∧ 0 < lo0) then ⟨0, 2⟩ else
    let mom := bx.map moments
    let delta : Int := mom.foldl (fun acc (d, _, _, _) => Max.max acc d.hi) 0
    let Rhi : Int := ONE + delta
    -- distinct centres
    let ctr := bx.map fun P => (P.xc, P.yc)
    let distinct := ctr.foldl (fun acc c => if acc.contains c then acc else acc ++ [c]) []
    match unionArea cs distinct Rhi cand with
    | none => ⟨0, 3⟩
    | some u =>
      let f := match phiAt k u.A.hi with | some (f0, _, _) => f0.lo | none => 0
      let lb := shrD (Max.max f 0 * lo0 * gmin) PR
      ⟨finish (Max.max lb 0), 0⟩
  else
  let needInt := nstr == 0 ∧ 0 < gmin
  let needExtra := nstr == 0 ∧ gmin < gmax ∧ 0 < gmax
  let needStr := nstr == 1 ∧ 0 < gmin
  if ¬(needInt ∨ needExtra ∨ needStr) then ⟨0, 5⟩ else
  let ctr := bx.map fun P => (P.xc, P.yc)
  match unionArea cs ctr ONE cand with
  | none => ⟨0, 3⟩
  | some u =>
  match remainder cs asinC bx pairs d2s with
  | none => ⟨0, 4⟩
  | some rr =>
    let A := u.A
    -- gradient in box coordinates
    let bv : List Iv := (List.range m).map fun d =>
      if d == 0 then u.gx.getD 1 default
      else if d % 2 == 1 then u.gx.getD ((d + 3) / 2) default else u.gy.getD ((d + 2) / 2) default
    let hw : List Int := (List.range m).map fun d => listGet hi d - listGet lo d
    let sumb : Int := (bv.zip hw).foldl (fun acc (b, h) => acc + (Iv.mul (Iv.abs b) (Iv.pt h)).hi) 0 / 2 + 1
    let Sb : Int := (bv.zip hw).foldl (fun acc (b, h) => acc + (Iv.sqr (Iv.mul b (Iv.pt h))).hi) 0 / 12 + 1
    let upA := A.hi + sumb + rr.Rmax
    let fminLo : Int := match phiAt k upA with
      | some (f, _, _) => Max.max (shrD (f.lo * lo0) PR) 0
      | none => 0
    let lowA := Max.max piLo (A.lo - sumb - rr.Rmax)
    match phiAt k lowA with
    | none => ⟨0, 6⟩
    | some (fLowA, _, _) =>
    let fmaxHi : Int := shrU (fLowA.hi * hi0) PR
    let tminLo := A.lo - sumb
    let er0 : Int := Max.max rr.Er 0
    let val : Int :=
      match phiAt k (A.hi + er0), phiAt k A.lo, phiAt k A.hi, phiAt k tminLo,
            phiAt k (A.lo + er0), phiAt k (A.hi + er0) with
      | some (fa, _, _), some (_, f1A, _), some (_, f1Ahi, _), some (_, _, f2),
        some (_, f1a1, _), some (_, f1a2, _) =>
        let h0 := Iv.pt (listGet hw 0)
        let b0 := bv.getD 0 default
        let r2c := Iv.pt ((lo0 + hi0) / 2)
        let f1Aiv : Iv := ⟨f1A.lo, f1Ahi.hi⟩                  -- φ'(A(c)), φ' increasing
        let t12 := Iv.divNat (Iv.mul (Iv.mul b0 h0) h0) 12      -- b0 h0²/12
        let sqSb := Iv.sqrt (Iv.pt Sb)
        let er := Iv.pt er0
        let ser2 := Iv.pt (Max.max rr.sEr2 0)
        let first := Iv.mul r2c (Iv.pt fa.lo)
        -- headline bracket: expansion at A(c)
        let wB := Iv.sqr (Iv.add sqSb ser2)
        let vB := Iv.sub (Iv.sub (Iv.add first (Iv.mul f1Aiv t12))
                  (Iv.div2e (Iv.mul (Iv.mul (Iv.abs f1Aiv) h0) er) 1))
                  (Iv.div2e (Iv.mul (Iv.mul wB (Iv.pt f2.hi)) h0) 2)
        -- second bracket: expansion at A(c) + Er
        let f1aiv : Iv := ⟨f1a1.lo, f1a2.hi⟩
        let wA := Iv.sqr (Iv.add sqSb (Iv.sqrt (Iv.add (Iv.sqr ser2) (Iv.sqr er))))
        let vA := Iv.sub (Iv.sub (Iv.add first (Iv.mul f1aiv t12))
                  (Iv.div2e (Iv.mul (Iv.mul (Iv.abs f1aiv) h0) er) 1))
                  (Iv.div2e (Iv.mul (Iv.mul wA (Iv.pt f2.hi)) h0) 2)
        if 0 < tminLo then Max.max (Max.max vB.lo vA.lo) 0 else 0
      | _, _, _, _, _, _ => 0
    let xlb : Int := if needInt then shrD (gmin * val) 0 else 0
    let elb : Int :=
      if needExtra then
        let undIdx := (List.range pairs.length).filter (fun p => st.getD p 0 == 2)
        let probs := undIdx.map fun p =>
          let (i, j) := pairs.getD p (0, 0)
          (p, i, j, probStrips (bx.getD i default) (bx.getD j default))
        let single := probs.foldl (fun best (p, _, _, (pin, pout)) =>
          let gp := gt.gmin (idx3 - pow3 p)
          let ga := gt.gmin (idx3 - 2 * pow3 p)
          let sc := (if gmin < gp then (gp - gmin) * evLB pin fminLo fmaxHi val else 0) +
                    (if gmin < ga then (ga - gmin) * evLB pout fminLo fmaxHi val else 0)
          Max.max best sc) 0
        let pairsBest := probs.foldl (fun best (p1, i1, j1, (pin1, pout1)) =>
          probs.foldl (fun best2 (p2, i2, j2, (pin2, pout2)) =>
            if p1 < p2 then
              let disjoint := i1 != i2 ∧ i1 != j2 ∧ j1 != i2 ∧ j1 != j2
              let sc := [(1, 1), (1, 0), (0, 1), (0, 0)].foldl (fun acc (s1, s2) =>
                let id := idx3 - (if s1 == 1 then pow3 p1 else 2 * pow3 p1)
                               - (if s2 == 1 then pow3 p2 else 2 * pow3 p2)
                let gs := gt.gmin id
                if gs ≤ gmin then acc else
                let q1 := if s1 == 1 then pin1 else pout1
                let q2 := if s2 == 1 then pin2 else pout2
                let q := if disjoint then shrD (q1 * q2) PR else Max.max (q1 + q2 - ONE) 0
                acc + (gs - gmin) * evLB q fminLo fmaxHi val) 0
              Max.max best2 sc
            else best2) best) 0
        Max.max single pairsBest
      else if needStr then
        match strad with
        | [j] =>
          let pord := Max.max (cdfIv (x j).xl (x j).xh (x (j + 1)).xl (x (j + 1)).xh 0).lo 0
          gmin * evLB pord fminLo fmaxHi val
        | _ => 0
      else 0
    ⟨finish (xlb + elb), 0⟩

end BHH.Cert
