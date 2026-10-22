/-
Module D, part 11: the leaf function with named pieces (`leafAlt`), equal to `leafLB` by `rfl` (no code change: the
production code is `leafLB`; the pieces only structure the proof).
-/
import BHH.Interfaces

namespace BHH.Cert

/-- the gradient of the union area in box coordinates (code enclosures) -/
def gradList (k : Nat) (u : UnionRes) : List Iv :=
  (List.range (2 * k - 3)).map fun d =>
    if d == 0 then u.gx.getD 1 default
    else if d % 2 == 1 then u.gx.getD ((d + 3) / 2) default else u.gy.getD ((d + 2) / 2) default

/-- the widths of the box -/
def widthList (k : Nat) (lo hi : List Int) : List Int :=
  (List.range (2 * k - 3)).map fun d => listGet hi d - listGet lo d

/-- `Σ_d |b_d| h_d / 2` rounded up -/
def sumAbs (bv : List Iv) (hw : List Int) : Int :=
  (bv.zip hw).foldl (fun acc (b, h) => acc + (Iv.mul (Iv.abs b) (Iv.pt h)).hi) 0 / 2 + 1

/-- `Σ_d (b_d h_d)² / 12` rounded up -/
def sumSq (bv : List Iv) (hw : List Int) : Int :=
  (bv.zip hw).foldl (fun acc (b, h) => acc + (Iv.sqr (Iv.mul b (Iv.pt h))).hi) 0 / 12 + 1

/-- lower bound of `r_2 φ(A)` on the box -/
def fminOf (k : Nat) (upA lo0 : Int) : Int :=
  match phiAt k upA with
  | some (f, _, _) => Max.max (shrD (f.lo * lo0) PR) 0
  | none => 0

/-- the value of the two brackets of Prop 3.4 -/
def bracketVal (k : Nat) (bv : List Iv) (hw : List Int) (A : Iv) (sumb Sb : Int) (rr : RemRes) (lo0 hi0 : Int) :
    Int :=
  let tminLo := A.lo - sumb
  let er0 : Int := Max.max rr.Er 0
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

/-- the undetermined edges with their probability bounds -/
def probsOf (bx : List PtBox) (pairs : List (Nat × Nat)) (st : List Nat) : List (Nat × Nat × Nat × (Int × Int)) :=
  let undIdx := (List.range pairs.length).filter (fun p => st.getD p 0 == 2)
  undIdx.map fun p =>
    let (i, j) := pairs.getD p (0, 0)
    (p, i, j, probStrips (bx.getD i default) (bx.getD j default))

/-- the extra term of Prop 3.6 with one undetermined edge -/
def singleLB (gt : GTab) (idx3 : Nat) (gmin : Int) (probs : List (Nat × Nat × Nat × (Int × Int)))
    (fminLo fmaxHi val : Int) : Int :=
  probs.foldl (fun best (p, _, _, (pin, pout)) =>
    let gp := gt.gmin (idx3 - pow3 p)
    let ga := gt.gmin (idx3 - 2 * pow3 p)
    let sc := (if gmin < gp then (gp - gmin) * evLB pin fminLo fmaxHi val else 0) +
              (if gmin < ga then (ga - gmin) * evLB pout fminLo fmaxHi val else 0)
    Max.max best sc) 0

/-- the extra term of Prop 3.6 with two undetermined edges -/
def pairsLB (gt : GTab) (idx3 : Nat) (gmin : Int) (probs : List (Nat × Nat × Nat × (Int × Int)))
    (fminLo fmaxHi val : Int) : Int :=
  probs.foldl (fun best (p1, i1, j1, (pin1, pout1)) =>
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

/-- the largest half-diagonal (upper bound) of the points of the box -/
def deltaOf (bx : List PtBox) : Int :=
  (bx.map moments).foldl (fun acc (d, _, _, _) => Max.max acc d.hi) 0

/-- the distinct centres, in order of first occurrence -/
def distinctOf (ctr : List (Int × Int)) : List (Int × Int) :=
  ctr.foldl (fun acc c => if acc.contains c then acc else acc ++ [c]) []

/-- the Prop 3.8 bound `r_2^- · gmin · φ(A^+)` before the volume factor -/
def p38lb (k : Nat) (u : UnionRes) (lo0 gmin : Int) : Int :=
  let f := match phiAt k u.A.hi with | some (f0, _, _) => f0.lo | none => 0
  shrD (Max.max f 0 * lo0 * gmin) PR

/-- the leaf function with named pieces -/
def leafAlt (k : Nat) (gt : GTab) (cs : Int → Iv × Iv) (cand : CandFn) (asinC : AsinFn)
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
    let delta : Int := deltaOf bx
    let Rhi : Int := ONE + delta
    -- distinct centres
    let ctr := bx.map fun P => (P.xc, P.yc)
    let distinct := distinctOf ctr
    match BHH.Cert.unionArea cs distinct Rhi cand with
    | none => ⟨0, 3⟩
    | some u =>
      let lb := p38lb k u lo0 gmin
      ⟨finish (Max.max lb 0), 0⟩
  else
  let needInt := nstr == 0 ∧ 0 < gmin
  let needExtra := nstr == 0 ∧ gmin < gmax ∧ 0 < gmax
  let needStr := nstr == 1 ∧ 0 < gmin
  if ¬(needInt ∨ needExtra ∨ needStr) then ⟨0, 5⟩ else
  let ctr := bx.map fun P => (P.xc, P.yc)
  match BHH.Cert.unionArea cs ctr ONE cand with
  | none => ⟨0, 3⟩
  | some u =>
  match remainder cs asinC bx pairs d2s with
  | none => ⟨0, 4⟩
  | some rr =>
    let A := u.A
    -- gradient in box coordinates
    let bv : List Iv := gradList k u
    let hw : List Int := widthList k lo hi
    let sumb : Int := sumAbs bv hw
    let Sb : Int := sumSq bv hw
    let upA := A.hi + sumb + rr.Rmax
    let fminLo : Int := fminOf k upA lo0
    let lowA := Max.max piLo (A.lo - sumb - rr.Rmax)
    match phiAt k lowA with
    | none => ⟨0, 6⟩
    | some (fLowA, _, _) =>
    let fmaxHi : Int := shrU (fLowA.hi * hi0) PR
    let val : Int := bracketVal k bv hw A sumb Sb rr lo0 hi0
    let xlb : Int := if needInt then shrD (gmin * val) 0 else 0
    let elb : Int :=
      if needExtra then
        let probs := probsOf bx pairs st
        let single := singleLB gt idx3 gmin probs fminLo fmaxHi val
        let pairsBest := pairsLB gt idx3 gmin probs fminLo fmaxHi val
        Max.max single pairsBest
      else if needStr then
        match strad with
        | [j] =>
          let pord := Max.max (cdfIv (x j).xl (x j).xh (x (j + 1)).xl (x (j + 1)).xh 0).lo 0
          gmin * evLB pord fminLo fmaxHi val
        | _ => 0
      else 0
    ⟨finish (xlb + elb), 0⟩

theorem leafLB_eq_alt (k : Nat) (gt : GTab) (cs : Int → Iv × Iv) (cand : CandFn) (asinC : AsinFn)
    (lo hi : List Int) : leafLB k gt cs cand asinC lo hi = leafAlt k gt cs cand asinC lo hi := rfl

end BHH.Cert
