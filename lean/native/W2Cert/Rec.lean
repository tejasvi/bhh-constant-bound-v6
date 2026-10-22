/-
The forward recursion of the window-2 bound (paper Section 4.4) for one value of `t`, in exact integer
arithmetic with one directed rounding per stored entry (core Lean only).

Cells `c = (ir, it)`; only the half `it < NT/2` is stored (the tables are mirror symmetric, so the recursion is).
`F(D, c)` is stored as `F_st(D, c) · 2^-E` with `F_st < 2^62`.  One step:
  `F'(D', c2) = w(ir2) Σ_{c} e^{-t ā(c, c2)} G_{N(c2), S(c,c2)}(D', c)`,  `G_{N,S}(D', c) = Σ_{D -> D'} F(D, c)`,
summed over all source cells `c` (a stored cell and its mirror image use the same `F`).  The closing sum for `k`
uses the closing values `Λ` of the pass instead of the transitions.  `lower = true` rounds every kernel and every
stored entry down (a lower bound of the exact recursion), `lower = false` rounds up.
-/
import W2Cert.Table
import W2Cert.Pass

namespace W2C
open BHH.Cert

/-- Transition and closing tables of the pass on the 17 reachable states (index `17` = dropped). -/
structure PassTab where
  trans : Array Nat     -- index ((s * 2 + a1) * 2 + a2)
  close2 : Array Nat    -- same index: twice the closing value
  init1 : Array Nat     -- [a1]: state after the first increment
  deriving Inhabited

def stIndex (s : St) : Nat := (reachable.findIdx? (· == s)).getD 17

def mkPassTab : PassTab :=
  let sts := reachable.toArray
  let idx := (List.range (17 * 4)).toArray
  let tr := idx.map fun q =>
    let s := sts[q / 4]!
    let a1 := (q / 2) % 2 == 1
    let a2 := q % 2 == 1
    match s.step a1 (if s.two then a2 else false) with
    | none => 17
    | some s' => stIndex s'
  let cl := idx.map fun q =>
    let s := sts[q / 4]!
    s.closeStep2 ((q / 2) % 2 == 1) (if s.two then q % 2 == 1 else false)
  let i1 := #[false, true].map fun a1 => match St.init.step a1 false with
    | none => 17
    | some s' => stIndex s'
  ⟨tr, cl, i1⟩

/-- `exp(-t ā)` at scale `2^-62` for `t = j / 2^dtl`, `ā = a / 2^PR` (`a` a multiple of `2^dtl`), rounded down
(`lower`) or up. -/
def kern (lower : Bool) (j dtl : Nat) (a : Int) : Nat :=
  let x : Int := -((j * a) / 2 ^ dtl)
  let e := expPt x
  if lower then (shrD e.lo (PR - 62)).toNat else (shrU e.hi (PR - 62)).toNat

/-- number of bits of `n` -/
def nbits (n : Nat) : Nat := Nat.log2 n + 1

/-- Round `v · 2^-sc` to a mantissa at scale `2^-E'` with `E' = sc - sh`: floor or ceil of `v / 2^sh`. -/
def rnd (lower : Bool) (v sh : Nat) : Nat :=
  if lower then v >>> sh else (v + (2 ^ sh - 1)) >>> sh

/-- Result of one `t`: for each `k`, twice the closing sum `Ψ_k` as `(mantissa, scale)`: value `m · 2^-sc`. -/
structure PsiOut where
  vals : Array (Nat × Nat)
  deriving Inhabited

/-- The recursion for one `t = j / 2^dtl` up to `kmax`. `tab[(ir * NR + ir2) * ND + (d + NT - 1)] = (class, ā)`
(symmetric in `d`), `ā` multiples of `2^dtl` at scale `2^-PR`. -/
def runT (g : Grid) (rings : Array Ring) (tab : Array (Nat × Int)) (pt : PassTab)
    (lower : Bool) (j dtl kmax : Nat) (par : Bool := false) : PsiOut := Id.run do
  let NR := g.NR
  let NT := g.NT
  let ND := g.ND
  let H := NT / 2
  let NCh := NR * H
  -- kernels for this t
  let kt : Array Nat := tab.map fun (_, a) => kern lower j dtl a
  -- first step: F_1(D, c) = [D = init1(N)] w(ir) e^{-t ubar(ir)}
  let w : Array Nat := rings.map fun R => R.areaLo.toNat          -- scale 2^-PR
  let f1 : Array Nat := rings.map fun R => kern lower j dtl (R.euHi + (2 ^ dtl - (R.euHi % 2 ^ dtl)) % 2 ^ dtl)
  -- F at scale 2^-(PR + 62): entries w * f1
  let mut F : Array Nat := Array.replicate (NCh * 17) 0
  for ir in [0:NR] do
    let D := pt.init1[if rings[ir]!.nflag then 1 else 0]!
    if D < 17 then
      for it in [0:H] do
        F := F.set! ((ir * H + it) * 17 + D) (w[ir]! * f1[ir]!)
  -- normalise to 62 bits
  let mx0 := F.foldl Max.max 0
  let sh0 := if nbits mx0 > 62 then nbits mx0 - 62 else 0
  F := F.map fun v => rnd lower v sh0
  let mut E : Nat := PR + 62 - sh0          -- F_true = F * 2^-E
  let mut out : Array (Nat × Nat) := Array.replicate (kmax + 1) (0, 0)
  for i in [1:kmax - 1] do
    -- pre-merge: G[N][S][c] (17 entries) and V[N][S][c]
    let mut G : Array Nat := Array.replicate (4 * NCh * 17) 0
    let mut V : Array Nat := Array.replicate (4 * NCh) 0
    for c in [0:NCh] do
      for D in [0:17] do
        let v := F[c * 17 + D]!
        if v != 0 then
          for ns in [0:4] do
            let D2 := pt.trans[(D * 2 + ns / 2) * 2 + ns % 2]!
            if D2 < 17 then
              G := G.modify ((ns * NCh + c) * 17 + D2) (· + v)
            let cv := pt.close2[(D * 2 + ns / 2) * 2 + ns % 2]!
            if cv != 0 then
              V := V.modify (ns * NCh + c) (· + cv * v)
    -- targets: one row (ring ir2) at a time, optionally in parallel tasks
    let G' := G
    let V' := V
    let rowOf (ir2 : Nat) : Array Nat × Nat := Id.run do
      let nb := if rings[ir2]!.nflag then 1 else 0
      let wt := w[ir2]!
      let mut rowF : Array Nat := Array.replicate (H * 17) 0
      let mut rowPsi : Nat := 0
      for it2 in [0:H] do
        let mut acc : Array Nat := Array.replicate 17 0
        let mut cacc : Nat := 0
        for ir in [0:NR] do
          let base := (ir * NR + ir2) * ND + (NT - 1)
          for it in [0:H] do
            let c := ir * H + it
            -- direct source (ir, it) and mirrored source (ir, NT-1-it), both with F(., c)
            for m in [0:2] do
              let itS := if m == 0 then it else NT - 1 - it
              let idx := base + it2 - itS
              let (cls, _) := tab[idx]!
              let K := kt[idx]!
              let ns := nb * 2 + (if cls == 1 then 1 else 0)
              for D2 in [0:17] do
                let gv := G'[(ns * NCh + c) * 17 + D2]!
                if gv != 0 then acc := acc.modify D2 (· + gv * K)
              let vv := V'[ns * NCh + c]!
              if vv != 0 then cacc := cacc + vv * K
        for D2 in [0:17] do
          rowF := rowF.set! (it2 * 17 + D2) (wt * acc[D2]!)
        rowPsi := rowPsi + wt * cacc
      return (rowF, rowPsi)
    let rows : List (Array Nat × Nat) :=
      if par then ((List.range NR).map fun ir2 => Task.spawn fun _ => rowOf ir2).map Task.get
      else (List.range NR).map rowOf
    let Fn : Array Nat := rows.foldl (fun acc r => acc ++ r.1) #[]
    let psi : Nat := rows.foldl (fun acc r => acc + r.2) 0
    -- closing sum for k = i + 2: value (sum over the half, times 2 for the mirror half) / 2 (close2 is 2 Λ)
    -- = psi * 2^-(E + 62 + PR)
    out := out.set! (i + 2) (psi, E + 62 + PR)
    -- normalise Fn
    let mx := Fn.foldl Max.max 0
    if mx == 0 then break
    let sh := if nbits mx > 62 then nbits mx - 62 else 0
    F := Fn.map fun v => rnd lower v sh
    E := E + 62 + PR - sh
  return ⟨out⟩

end W2C

namespace W2C
open BHH.Cert

/-! ## Faster recursion: scalar arithmetic only (all `Nat` values stay below `2^63`)

Stored `F < 2^57` at scale `2^-E`; pre-merged `G = g1 2^31 + g0 < 2^62`, `V = v1 2^31 + v0 < 2^62`; kernels
`K = k1 2^31 + k0 < 2^62` at scale `2^-62`.  A product contributes `⌊g1 k1 / 2^14⌋ + ⌊(g1 k0 + g0 k1) / 2^45⌋` to
the lower accumulator (`≤ G K / 2^76`), and that plus `3` to the upper one (`> G K / 2^76`); at most `2^14` terms per
accumulator keep it below `2^63`. -/

def m31 : Nat := 2 ^ 31 - 1

/-- `⌊G K / 2^76⌋`-type lower (or upper, `+3`) contribution of one product from the 31-bit halves. -/
@[inline] def mulTop (lower : Bool) (g1 g0 k1 k0 : Nat) : Nat :=
  let t := (g1 * k1) >>> 14 + (g1 * k0 + g0 * k1) >>> 45
  if lower then t else t + 3

/-- `e^{-ā 2^-dtl}` at scale `2^-PR`, rounded down (`lower`) or up, for `ā = a / 2^PR` (`a` a multiple of `2^dtl`). -/
def kern1 (lower : Bool) (dtl : Nat) (a : Int) : Nat :=
  let e := expPt (-(a / 2 ^ dtl))
  if lower then e.lo.toNat else e.hi.toNat

/-- `x^j` for `x` at scale `2^-PR` (`x ≤ 2^PR`), rounded down (`lower`) or up at every multiplication, by squaring. -/
def powFix (lower : Bool) (x : Nat) : Nat → Nat
  | 0 => 2 ^ PR
  | j + 1 =>
    let h := powFix lower x ((j + 1) / 2)
    let h2 := if lower then (h * h) >>> PR else (h * h + 2 ^ PR - 1) >>> PR
    if (j + 1) % 2 == 0 then h2
    else if lower then (h2 * x) >>> PR else (h2 * x + 2 ^ PR - 1) >>> PR
  decreasing_by omega

/-- Kernels `e^{-t ā}` at scale `2^-62` for `t = j 2^-dtl` from `e1 = e^{-ā 2^-dtl}` (scale `2^-PR`). -/
def kernFromE1 (lower : Bool) (j : Nat) (e1 : Nat) : Nat :=
  let p := powFix lower e1 j
  if lower then p >>> (PR - 62) else (p + 2 ^ (PR - 62) - 1) >>> (PR - 62)

/-- Add the contributions of the nonzero entries `lst` of `G` (row `o`) times `K = k1 2^31 + k0` to `acc`. -/
def addList (lower : Bool) (G1 G0 : Array Nat) (o k1 k0 : Nat) : List Nat → Array Nat → Array Nat
  | [], acc => acc
  | D2 :: rest, acc =>
    let x := mulTop lower G1[o * 17 + D2]! G0[o * 17 + D2]! k1 k0
    addList lower G1 G0 o k1 k0 rest (acc.set! D2 (acc[D2]! + x))

/-- All source cells `c < n` (stored half, each with its mirror image) for the target `(ir2, it2)`. -/
def srcLoop (lower : Bool) (NR NT ND H NCh nb ir2 it2 : Nat) (k1s k0s : Array Nat) (cls1 : Array Bool)
    (G1 G0 V1 V0 : Array Nat) (nz : Array (List Nat)) : Nat → Array Nat → Nat → Array Nat × Nat
  | 0, acc, cacc => (acc, cacc)
  | c + 1, acc, cacc =>
    let ir := c / H
    let it := c % H
    let base := (ir * NR + ir2) * ND + (NT - 1)
    -- direct source
    let idx := base + it2 - it
    let k1 := k1s[idx]!
    let k0 := k0s[idx]!
    let o := (nb * 2 + (if cls1[idx]! then 1 else 0)) * NCh + c
    let acc := addList lower G1 G0 o k1 k0 nz[o]! acc
    let cacc := cacc + mulTop lower V1[o]! V0[o]! k1 k0
    -- mirrored source
    let idx' := base + it2 - (NT - 1 - it)
    let k1' := k1s[idx']!
    let k0' := k0s[idx']!
    let o' := (nb * 2 + (if cls1[idx']! then 1 else 0)) * NCh + c
    let acc := addList lower G1 G0 o' k1' k0' nz[o']! acc
    let cacc := cacc + mulTop lower V1[o']! V0[o']! k1' k0'
    srcLoop lower NR NT ND H NCh nb ir2 it2 k1s k0s cls1 G1 G0 V1 V0 nz c acc cacc

/-- The fast recursion for one `t` (same interface and meaning as `runT`). -/
def runT2 (g : Grid) (rings : Array Ring) (tab : Array (Nat × Int)) (e1 : Array Nat) (pt : PassTab)
    (lower : Bool) (j dtl kmax : Nat) (par : Bool := false) : PsiOut := Id.run do
  let NR := g.NR
  let NT := g.NT
  let ND := g.ND
  let H := NT / 2
  let NCh := NR * H
  let kt : Array Nat := e1.map fun x => kernFromE1 lower j x
  let k1s : Array Nat := kt.map (· >>> 31)
  let k0s : Array Nat := kt.map (· &&& m31)
  let cls1 : Array Bool := tab.map fun (c, _) => c == 1
  let w : Array Nat := rings.map fun R => R.areaLo.toNat
  let f1 : Array Nat := rings.map fun R => kern lower j dtl (R.euHi + (2 ^ dtl - (R.euHi % 2 ^ dtl)) % 2 ^ dtl)
  let mut F : Array Nat := Array.replicate (NCh * 17) 0
  for ir in [0:NR] do
    let D := pt.init1[if rings[ir]!.nflag then 1 else 0]!
    if D < 17 then
      for it in [0:H] do
        F := F.set! ((ir * H + it) * 17 + D) (w[ir]! * f1[ir]!)
  let mx0 := F.foldl Max.max 0
  let sh0 := if nbits mx0 > 57 then nbits mx0 - 57 else 0
  F := F.map fun v => rnd lower v sh0
  let mut E : Nat := PR + 62 - sh0
  let mut out : Array (Nat × Nat) := Array.replicate (kmax + 1) (0, 0)
  for i in [1:kmax - 1] do
    -- pre-merge into halves
    let mut G1 : Array Nat := Array.replicate (4 * NCh * 17) 0
    let mut G0 : Array Nat := Array.replicate (4 * NCh * 17) 0
    let mut V1 : Array Nat := Array.replicate (4 * NCh) 0
    let mut V0 : Array Nat := Array.replicate (4 * NCh) 0
    let mut nz : Array (List Nat) := Array.replicate (4 * NCh) []
    for c in [0:NCh] do
      for ns in [0:4] do
        let mut gs : Array Nat := Array.replicate 17 0
        let mut vs : Nat := 0
        for D in [0:17] do
          let v := F[c * 17 + D]!
          if v != 0 then
            let q := (D * 2 + ns / 2) * 2 + ns % 2
            let D2 := pt.trans[q]!
            if D2 < 17 then gs := gs.modify D2 (· + v)
            vs := vs + pt.close2[q]! * v
        let mut lst : List Nat := []
        for D2 in [0:17] do
          let v := gs[16 - D2]!
          if v != 0 then
            lst := (16 - D2) :: lst
            G1 := G1.set! ((ns * NCh + c) * 17 + (16 - D2)) (v >>> 31)
            G0 := G0.set! ((ns * NCh + c) * 17 + (16 - D2)) (v &&& m31)
        nz := nz.set! (ns * NCh + c) lst
        V1 := V1.set! (ns * NCh + c) (vs >>> 31)
        V0 := V0.set! (ns * NCh + c) (vs &&& m31)
    let rowOf (ir2 : Nat) : Array Nat × Nat := Id.run do
      let nb := if rings[ir2]!.nflag then 1 else 0
      let wt := w[ir2]!
      let mut rowF : Array Nat := Array.replicate (H * 17) 0
      let mut rowPsi : Nat := 0
      for it2 in [0:H] do
        let (acc, cacc) := srcLoop lower NR NT ND H NCh nb ir2 it2 k1s k0s cls1 G1 G0 V1 V0 nz NCh
          (Array.replicate 17 0) 0
        for D2 in [0:17] do
          rowF := rowF.set! (it2 * 17 + D2) (wt * acc[D2]!)
        rowPsi := rowPsi + wt * cacc
      return (rowF, rowPsi)
    let rows : List (Array Nat × Nat) :=
      if par then ((List.range NR).map fun ir2 => Task.spawn fun _ => rowOf ir2).map Task.get
      else (List.range NR).map rowOf
    let Fn : Array Nat := rows.foldl (fun acc r => acc ++ r.1) #[]
    let psi : Nat := rows.foldl (fun acc r => acc + r.2) 0
    -- acc is at scale 2^-(E + 62 - 76) = 2^-(E - 14); times w at 2^-PR
    out := out.set! (i + 2) (psi, E - 14 + PR)
    let mx := Fn.foldl Max.max 0
    if mx == 0 then break
    let sh := if nbits mx > 57 then nbits mx - 57 else 0
    F := Fn.map fun v => rnd lower v sh
    E := E - 14 + PR - sh
  return ⟨out⟩

end W2C

namespace W2C
open BHH.Cert

/-! ## The production recursion (full grid, no mirror folding, raw tables)

Cells `c = ir * NT + it` (`ir < NR`, `it < NT`), all stored.  Table index of the pair `(c, c2)`:
`(ir * NR + ir2) * ND + (it2 + NT - 1 - it)` (offset `d = it2 - it`). -/

/-- All source cells `c < n` for the target `(ir2, it2)` (full grid). -/
def srcLoopF (lower : Bool) (NR NT ND NC nb ir2 it2 : Nat) (k1s k0s : Array Nat) (cls1 : Array Bool)
    (G1 G0 V1 V0 : Array Nat) (nz : Array (List Nat)) : Nat → Array Nat → Nat → Array Nat × Nat
  | 0, acc, cacc => (acc, cacc)
  | c + 1, acc, cacc =>
    let ir := c / NT
    let it := c % NT
    let idx := (ir * NR + ir2) * ND + (it2 + (NT - 1) - it)
    let k1 := k1s[idx]!
    let k0 := k0s[idx]!
    let o := (nb * 2 + (if cls1[idx]! then 1 else 0)) * NC + c
    let acc := addList lower G1 G0 o k1 k0 nz[o]! acc
    let cacc := cacc + mulTop lower V1[o]! V0[o]! k1 k0
    srcLoopF lower NR NT ND NC nb ir2 it2 k1s k0s cls1 G1 G0 V1 V0 nz c acc cacc

/-- Pre-merged entry: `G_{N,S}(D2, c) = Σ_{D -> D2} F(D, c)` and `V_{N,S}(c) = Σ_D close2(D) F(D, c)`. -/
def gEntry (pt : PassTab) (F : Array Nat) (ns c D2 : Nat) : Nat :=
  (List.range 17).foldl (fun acc D =>
    if pt.trans[(D * 2 + ns / 2) * 2 + ns % 2]! == D2 then acc + F[c * 17 + D]! else acc) 0

def vEntry (pt : PassTab) (F : Array Nat) (ns c : Nat) : Nat :=
  (List.range 17).foldl (fun acc D => acc + pt.close2[(D * 2 + ns / 2) * 2 + ns % 2]! * F[c * 17 + D]!) 0

/-- The production recursion for one `t` (full grid).  Output: for each `k`, `(Ψ value, scale)` meaning
`value · 2^-scale` is a lower (`lower`) or upper bound of `Ψ_k^d(t)`. -/
def runT3 (g : Grid) (rings : Array Ring) (tab : Array (Nat × Int)) (e1 : Array Nat) (pt : PassTab)
    (lower : Bool) (j dtl kmax : Nat) : PsiOut := Id.run do
  let NR := g.NR
  let NT := g.NT
  let ND := g.ND
  let NC := NR * NT
  let kt : Array Nat := e1.map fun x => kernFromE1 lower j x
  let k1s : Array Nat := kt.map (· >>> 31)
  let k0s : Array Nat := kt.map (· &&& m31)
  let cls1 : Array Bool := tab.map fun (c, _) => c == 1
  let w : Array Nat := rings.map fun R => R.areaLo.toNat
  let f1 : Array Nat := rings.map fun R => kern lower j dtl (R.euHi + (2 ^ dtl - (R.euHi % 2 ^ dtl)) % 2 ^ dtl)
  -- F_1(D, c) = [D = init1(N(ir))] w(ir) e^{-t ub(ir)}, scale 2^-(PR + 62)
  let F0 : Array Nat := Array.ofFn (n := NC * 17) fun q =>
    let c := q.val / 17
    let D := q.val % 17
    let ir := c / NT
    if pt.init1[if rings[ir]!.nflag then 1 else 0]! == D then w[ir]! * f1[ir]! else 0
  let mx0 := F0.foldl Max.max 0
  let sh0 := if nbits mx0 > 57 then nbits mx0 - 57 else 0
  let mut F : Array Nat := F0.map fun v => rnd lower v sh0
  let mut E : Nat := PR + 62 - sh0
  let mut out : Array (Nat × Nat) := Array.replicate (kmax + 1) (0, 0)
  for i in [1:kmax - 1] do
    let Fc := F
    let G : Array Nat := Array.ofFn (n := 4 * NC * 17) fun q =>
      gEntry pt Fc (q.val / (NC * 17)) ((q.val / 17) % NC) (q.val % 17)
    let G1 : Array Nat := G.map (· >>> 31)
    let G0 : Array Nat := G.map (· &&& m31)
    let V : Array Nat := Array.ofFn (n := 4 * NC) fun q => vEntry pt Fc (q.val / NC) (q.val % NC)
    let V1 : Array Nat := V.map (· >>> 31)
    let V0 : Array Nat := V.map (· &&& m31)
    let nz : Array (List Nat) := Array.ofFn (n := 4 * NC) fun q =>
      (List.range 17).filter fun D2 => G[q.val * 17 + D2]! != 0
    let tgt (c2 : Nat) : Array Nat × Nat :=
      let ir2 := c2 / NT
      let it2 := c2 % NT
      let nb := if rings[ir2]!.nflag then 1 else 0
      let (acc, cacc) := srcLoopF lower NR NT ND NC nb ir2 it2 k1s k0s cls1 G1 G0 V1 V0 nz NC
        (Array.replicate 17 0) 0
      (acc.map (w[ir2]! * ·), w[ir2]! * cacc)
    let rows : Array (Array Nat × Nat) := Array.ofFn (n := NC) fun c2 => tgt c2.val
    let Fn : Array Nat := rows.foldl (fun acc r => acc ++ r.1) #[]
    let psi : Nat := rows.foldl (fun acc r => acc + r.2) 0
    -- acc at scale 2^-(E + 62 - 76), times w (2^-PR); psi counts 2 Λ, so halve the value: scale + 1
    out := out.set! (i + 2) (psi, E - 14 + PR + 1)
    let mx := Fn.foldl Max.max 0
    if mx == 0 then break
    let sh := if nbits mx > 57 then nbits mx - 57 else 0
    F := Fn.map fun v => rnd lower v sh
    E := E - 14 + PR - sh
  return ⟨out⟩

end W2C

namespace W2C
open BHH.Cert

/-! ## The production recursion in explicit-recursion form (`runT4`, same arithmetic as `runT3`) -/

/-- Read-only data of one run: grid sizes, kernel halves, classes, weights, pre-merge tables. -/
structure RecData where
  NR : Nat
  NT : Nat
  ND : Nat
  NC : Nat
  k1s : Array Nat
  k0s : Array Nat
  cls1 : Array Bool
  w : Array Nat
  nb : Array Nat      -- per ring: 1 if the edge {i+1, i} is sure
  pt : PassTab
  deriving Inhabited

/-- One step: from the stored `F` (entries `< 2^57`), the unnormalised next `Fn` (entry `(c2, D2)` at index
`c2 * 17 + D2`) and the closing sum `psi` (twice the value). -/
def recStep (lower : Bool) (rd : RecData) (F : Array Nat) : Array Nat × Nat :=
  let NC := rd.NC
  let G : Array Nat := Array.ofFn (n := 4 * NC * 17) fun q =>
    gEntry rd.pt F (q.val / (NC * 17)) ((q.val / 17) % NC) (q.val % 17)
  let G1 : Array Nat := G.map (· >>> 31)
  let G0 : Array Nat := G.map (· &&& m31)
  let V : Array Nat := Array.ofFn (n := 4 * NC) fun q => vEntry rd.pt F (q.val / NC) (q.val % NC)
  let V1 : Array Nat := V.map (· >>> 31)
  let V0 : Array Nat := V.map (· &&& m31)
  let nz : Array (List Nat) := Array.ofFn (n := 4 * NC) fun q =>
    (List.range 17).filter fun D2 => G[q.val * 17 + D2]! != 0
  let tgt (c2 : Nat) : Array Nat × Nat :=
    let ir2 := c2 / rd.NT
    let it2 := c2 % rd.NT
    let (acc, cacc) := srcLoopF lower rd.NR rd.NT rd.ND NC rd.nb[ir2]! ir2 it2 rd.k1s rd.k0s rd.cls1
      G1 G0 V1 V0 nz NC (Array.replicate 17 0) 0
    (acc.map (rd.w[ir2]! * ·), rd.w[ir2]! * cacc)
  let rows : Array (Array Nat × Nat) := Array.ofFn (n := NC) fun c2 => tgt c2.val
  (Array.ofFn (n := NC * 17) fun q => rows[q.val / 17]!.1[q.val % 17]!,
   (List.range NC).foldl (fun acc c2 => acc + rows[c2]!.2) 0)

/-- Normalise to entries `< 2^57`: `(F', sh)` with `F' = round(Fn / 2^sh)`. -/
def normF (lower : Bool) (Fn : Array Nat) : Array Nat × Nat :=
  let mx := Fn.foldl Max.max 0
  let sh := if nbits mx > 57 then nbits mx - 57 else 0
  (Fn.map fun v => rnd lower v sh, sh)

/-- Steps `i = 1, 2, ...` (fuel `n`); `F` at scale `2^-E` (`E : Int`, it becomes negative when the values grow).
Appends `(psi, scale)` for `k = i + 2` (psi counts `2 Λ`, hence the extra `+ 1` in the scale). -/
def recIter (lower : Bool) (rd : RecData) : Nat → Array Nat → Int → List (Nat × Int) → List (Nat × Int)
  | 0, _, _, out => out
  | n + 1, F, E, out =>
    let (Fn, psi) := recStep lower rd F
    let out' := out ++ [(psi, E - 14 + (PR : Int) + 1)]
    let (F', sh) := normF lower Fn
    recIter lower rd n F' (E - 14 + (PR : Int) - (sh : Int)) out'

/-- The production recursion for one `t = j 2^-dtl`: the list of `(Ψ value, scale)` for `k = 3, ..., kmax`
(value `· 2^-scale` is a lower (`lower`) or upper bound of `Ψ^d_k(t)`). -/
def runT4 (g : Grid) (rings : Array Ring) (tab : Array (Nat × Int)) (e1 : Array Nat) (pt : PassTab)
    (lower : Bool) (j dtl kmax : Nat) : List (Nat × Int) :=
  let NR := g.NR
  let NT := g.NT
  let NC := NR * NT
  let kt : Array Nat := e1.map fun x => kernFromE1 lower j x
  let rd : RecData := ⟨NR, NT, g.ND, NC, kt.map (· >>> 31), kt.map (· &&& m31), tab.map (·.1 == 1),
    rings.map (·.areaLo.toNat), rings.map (fun R => if R.nflag then 1 else 0), pt⟩
  let f1 : Array Nat := rings.map fun R => kern lower j dtl (R.euHi + (2 ^ dtl - (R.euHi % 2 ^ dtl)) % 2 ^ dtl)
  let F0 : Array Nat := Array.ofFn (n := NC * 17) fun q =>
    let c := q.val / 17
    let D := q.val % 17
    let ir := c / NT
    if pt.init1[rd.nb[ir]!]! == D then rd.w[ir]! * f1[ir]! else 0
  let (F1, sh0) := normF lower F0
  recIter lower rd (kmax - 2) F1 ((PR : Int) + 62 - (sh0 : Int)) []

end W2C
