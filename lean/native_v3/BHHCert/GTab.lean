/-
The g-table check (core Lean only; compiled, so that track N runs it by `native_decide`, and kernel-friendly:
structural recursion, `Nat`/`Int`/`List` only).

For an edge mask `e` on `k` vertices (pairs in the order of `pairList k`), `g2lb k e` is a lower bound for twice
Dong-Cao's `g` of the graph, proved in `BHH/Graph.lean` from the checks below only:
* `connB`: every vertex other than `0` has a neighbour strictly closer to `0` (distances by relaxation, unverified);
* `d2B`: `2D = Σ_v (2 - d(v))_+`, exact;
* `ccLB k e S`: for the vertex set `S` (a bitmask), a labelling of the other vertices that is constant along edges
  (label propagation, unverified; `respectsB` is the check) gives `cc(G - S) ≥ #{v ∉ S : label v = v}`;
* `qLB`: the largest of `1` and `ccLB k e S - |S|` over all `S`.
`checkTab k gmin` checks `gmin idx ≤ g2lb k e` for every edge state `idx` and every completion `e`.
-/
import BHHCert.Leaf

namespace BHH.Cert

/-- `f i = true` for all `i < n` (tail-recursive, kernel-friendly) -/
def allBelow (f : Nat → Bool) : Nat → Bool
  | 0 => true
  | n + 1 => if f n then allBelow f n else false

/-- adjacency of the graph with edge mask `e` on `k` vertices -/
def adjB (k e : Nat) (i j : Nat) : Bool :=
  i != j && (List.range (pairList k).length).any fun p =>
    ((pairList k).getD p (0, 0) == (i, j) || (pairList k).getD p (0, 0) == (j, i)) && e.testBit p

/-! ## connectivity -/

/-- one round of relaxation of the distances to vertex `0` (`k + 1` stands for infinity) -/
def bfsStep (k e : Nat) (d : List Nat) : List Nat :=
  (List.range k).map fun v =>
    (List.range k).foldl (fun acc u => if adjB k e u v then min acc (d.getD u (k + 1) + 1) else acc)
      (d.getD v (k + 1))

/-- distances to vertex `0` after `k` rounds (unverified) -/
def bfsDist (k e : Nat) : List Nat :=
  Nat.repeat (bfsStep k e) k ((List.range k).map fun v => if v = 0 then 0 else k + 1)

/-- connectivity check: every vertex other than `0` has a neighbour strictly closer to `0` -/
def connB (k e : Nat) : Bool :=
  let d := bfsDist k e
  (List.range k).all fun v =>
    v == 0 || (List.range k).any fun u => adjB k e u v && decide (d.getD u 0 < d.getD v 0)

/-! ## degrees -/

/-- the degree of `v` -/
def degB (k e : Nat) (v : Nat) : Nat := (List.finRange k).countP fun (u : Fin k) => adjB k e v u.val

/-- `2D = Σ_v (2 - d(v))_+` -/
def d2B (k e : Nat) : Int := ((List.finRange k).map fun (v : Fin k) => max (2 - (degB k e v.val : Int)) 0).sum

/-! ## components after deleting `S` -/

/-- one round of label propagation among the vertices outside the bitmask `S` -/
def labStep (k e S : Nat) (f : List Nat) : List Nat :=
  (List.range k).map fun v =>
    (List.range k).foldl (fun acc u =>
      if !S.testBit u && !S.testBit v && adjB k e v u then min acc (f.getD u 0) else acc) (f.getD v 0)

/-- labels after `k` rounds, starting from `label v = v` (unverified) -/
def labels (k e S : Nat) : List Nat := Nat.repeat (labStep k e S) k (List.range k)

/-- the labelling `f` is constant along the edges among the vertices outside `S` -/
def respectsB (k e S : Nat) (f : List Nat) : Bool :=
  (List.finRange k).all fun (u : Fin k) => (List.finRange k).all fun (v : Fin k) =>
    S.testBit u.val || S.testBit v.val || !adjB k e u.val v.val || f.getD u.val 0 == f.getD v.val 0

/-- certified lower bound for `cc(G - S) - |S|` (`1`, a bound for `q` anyway, if the check fails) -/
def ccLB (k e S : Nat) : Int :=
  let f := labels k e S
  if respectsB k e S f then
    (((List.finRange k).countP fun (v : Fin k) => !S.testBit v.val && f.getD v.val 0 == v.val : Nat) : Int) -
      (((List.finRange k).countP fun (v : Fin k) => S.testBit v.val : Nat) : Int)
  else 1

/-- certified lower bound for `q` -/
def qLB (k e : Nat) : Int := (List.range (2 ^ k)).foldl (fun acc S => max acc (ccLB k e S)) 1

/-- certified lower bound for `2g` -/
def g2lb (k e : Nat) : Int := if connB k e then 2 * qLB k e - d2B k e else 0

/-! ## the table check -/

/-- the digits `p < n` of the edge state `idx` (base 3) are compatible with the bits of `e` -/
def digitsOK (idx e : Nat) : Nat → Bool
  | 0 => true
  | p + 1 => if (idx / 3 ^ p % 3 != 1 || e.testBit p) && (idx / 3 ^ p % 3 != 0 || !e.testBit p) then
      digitsOK idx e p else false

/-- `2g` lower bounds of all graphs on `k` vertices, indexed by the edge mask -/
def g2arr (k : Nat) : Array Int := ((List.range (2 ^ (pairList k).length)).map (g2lb k)).toArray

/-- the table check: `gmin idx ≤ g2lb k e` for every state `idx < 3^np` and every completion `e < 2^np` -/
def checkTab (k : Nat) (gmin : Nat → Int) : Bool :=
  let np := (pairList k).length
  let arr := g2arr k
  allBelow (fun idx =>
    let g := gmin idx
    allBelow (fun e => !digitsOK idx e np || decide (g ≤ arr.getD e 0)) (2 ^ np)) (3 ^ np)

end BHH.Cert
