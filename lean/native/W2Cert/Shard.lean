/-
Shard checks for `native_decide` (track N).  A shard covers a list of grid points `t_j = j 2^-dtl`.  It recomputes
the tables (exact interval arithmetic), the kernels and both directed recursions for each of its `t_j`, and checks
claimed bounds `lo_{k,j} ≤ Ψ^d_k(t_j) ≤ hi_{k,j}` (claims are `(m, e)` pairs standing for `m 2^-e`).
-/
import W2Cert.Rec
import W2Cert.TInt

namespace W2C
open BHH.Cert

/-- The production parameters: grid 60/30/144, Riemann sums with 64 sub-intervals, vertex pruning; `dt = 2^-4`,
`T = 6`, `k ≤ 30`. -/
def prodGrid : Grid := ⟨60, 30, 144, 64, true⟩
def prodDtl : Nat := 4
def prodKmax : Nat := 30

/-- All shared data of a run: rings, symmetrised table (ā rounded up to multiples of `2^dtl` at scale `2^-PR`),
`e1 = e^{-ā 2^-dtl}` lower and upper, pass tables. -/
structure RunData where
  rings : Array Ring
  tab : Array (Nat × Int)
  e1lo : Array Nat
  e1hi : Array Nat
  pt : PassTab
  deriving Inhabited

/-- The symmetrised table from the raw entries `raw[(ir * NR + ir2) * ND + di]`. -/
def symTab (g : Grid) (dtl : Nat) (raw : Array (Nat × Int)) : Array (Nat × Int) :=
  let q := 2 ^ dtl
  (Array.range raw.size).map fun idx =>
    let di := idx % g.ND
    let base := idx - di
    let (c1, a1) := raw[idx]!
    let (c2, a2) := raw[base + (g.ND - 1 - di)]!
    let a := Max.max (Max.max a1 a2) 0
    (if c1 == c2 then c1 else 2, a + (q - a % q) % q)

/-- The production table: raw entries (no symmetrisation), `ā` clamped at `0` and rounded up to a multiple of
`2^dtl` (scale `2^-PR`). -/
def prepTab (dtl : Nat) (raw : Array (Nat × Int)) : Array (Nat × Int) :=
  let q := 2 ^ dtl
  raw.map fun (c, a) => let a := Max.max a 0; (c, a + (q - a % q) % q)

/-- Raw table entries, computed in parallel over the rings `ir` (`par`). -/
def rawTab (g : Grid) (rings : Array Ring) (par : Bool) : Array (Nat × Int) :=
  let ad := mkAData g
  let dtab := mkDTab g
  let rowOf (ir : Nat) : Array (Nat × Int) :=
    (Array.range (g.NR * g.ND)).map fun q => entryF g.prune rings ad dtab[q % g.ND]! ir (q / g.ND)
  let rows : List (Array (Nat × Int)) :=
    if par then ((List.range g.NR).map fun ir => Task.spawn fun _ => rowOf ir).map Task.get
    else (List.range g.NR).map rowOf
  rows.foldl (· ++ ·) #[]

def mkRunData (g : Grid) (dtl : Nat) (par : Bool) : RunData :=
  let rings := (Array.range g.NR).map (mkRing g)
  let tab := prepTab dtl (rawTab g rings par)
  let e1 (lower : Bool) : Array Nat :=
    if par then
      let n := tab.size
      let chunk := (n + 63) / 64
      let parts := (List.range 64).map fun p => Task.spawn fun _ =>
        (Array.range (Min.min chunk (n - Min.min n (p * chunk)))).map fun i => kern1 lower dtl tab[p * chunk + i]!.2
      parts.foldl (fun acc t => acc ++ t.get) #[]
    else tab.map fun (_, a) => kern1 lower dtl a
  ⟨rings, tab, e1 true, e1 false, mkPassTab⟩

/-- `a 2^-ea ≤ b 2^-eb` for integer exponents -/
def leScaled (a : Nat) (ea : Int) (b : Nat) (eb : Int) : Bool :=
  let m := Min.min ea eb
  a * 2 ^ (eb - m).toNat ≤ b * 2 ^ (ea - m).toNat

/-- Claims for one `t_j`: `(j, [(k, loM, loE, hiM, hiE)])`, standing for `loM 2^-loE ≤ Ψ_k(t_j) ≤ hiM 2^-hiE`. -/
abbrev TClaim := Nat × List (Nat × Nat × Int × Nat × Int)

/-- Check the claims of one `t_j` against the directed recursions (`runT4`: entry `k - 3` is `k`), given the
two outputs. -/
def checkClaims (kmax : Nat) (lo hi : Array (Nat × Int)) (c : TClaim) : Bool :=
  let (j, lst) := c
  1 ≤ j && lst.all fun (k, lm, le, hm, he) =>
    3 ≤ k && k ≤ kmax &&
    (let (pl, sl) := lo[k - 3]!
     let (ph, sh) := hi[k - 3]!
     leScaled lm le pl sl && leScaled ph sh hm he)

/-- Check the claims of one `t_j` against both directed recursions. -/
def checkT (g : Grid) (dtl kmax : Nat) (rd : RunData) (c : TClaim) : Bool :=
  checkClaims kmax (runT4 g rd.rings rd.tab rd.e1lo rd.pt true c.1 dtl kmax).toArray
    (runT4 g rd.rings rd.tab rd.e1hi rd.pt false c.1 dtl kmax).toArray c

/-- A shard: all its `t_j` checked (with `par`, one task per `t_j` and direction). -/
def shardOK (g : Grid) (dtl kmax : Nat) (par : Bool) (cs : List TClaim) : Bool :=
  let rd := mkRunData g dtl par
  if par then
    let tasks := cs.map fun c =>
      (c, Task.spawn fun _ => (runT4 g rd.rings rd.tab rd.e1lo rd.pt true c.1 dtl kmax).toArray,
          Task.spawn fun _ => (runT4 g rd.rings rd.tab rd.e1hi rd.pt false c.1 dtl kmax).toArray)
    tasks.all fun (c, tl, th) => checkClaims kmax tl.get th.get c
  else cs.all (checkT g dtl kmax rd)

end W2C

namespace W2C
open BHH.Cert

/-- The lower bounds `L[k][j] ≤ log Ψ_k(t_j) ≤ H[k][j]` from the claims (`none` if some `(k, j)` is missing or a
lower claim is `0`). -/
def claimLogs (ntv kmax : Nat) (cs : List TClaim) : Option (Array (Array Int) × Array (Array Int)) :=
  let empty : Array (Array (Option (Int × Int))) := Array.replicate (kmax + 1) (Array.replicate (ntv + 1) none)
  let filled := cs.foldl (fun acc (j, lst) =>
    lst.foldl (fun acc2 (k, lm, le, hm, he) =>
      if k ≤ kmax ∧ 1 ≤ j ∧ j ≤ ntv ∧ 0 < lm then
        acc2.modify k (·.set! j (some (logScaled true lm le, logScaled false hm he)))
      else acc2) acc) empty
  let ok := (List.range (kmax - 2)).all fun k0 => (List.range ntv).all fun j0 =>
    (filled[k0 + 3]!)[j0 + 1]!.isSome
  if ok then
    some (filled.map (·.map fun o => (o.getD (0, 0)).1), filled.map (·.map fun o => (o.getD (0, 0)).2))
  else none

/-- `Σ_{k=6}^{kmax} C_k ≥ num/den` follows from the claims: every `(k, j)` is claimed, and the sum of the
lower bounds `ckLo` (scale `2^-PR`) is at least `num/den`. -/
def tintOK (dtl T kmax lsub : Nat) (cs : List TClaim) (num den : Nat) : Bool :=
  let ntv := T * 2 ^ dtl
  match claimLogs ntv kmax cs with
  | none => false
  | some (L, H) =>
    let logs := logTable (ntv * 2 ^ lsub) (dtl + lsub)
    let tot := (List.range (kmax - 5)).foldl (fun acc k0 =>
      acc + ckLo (k0 + 6) dtl ntv lsub L[k0 + 6]! H[k0 + 6]! logs) 0
    decide (0 < den) && decide ((num : Int) * ONE ≤ tot * den)

end W2C
