/-
The exact bisection tree (core Lean; kernel-friendly except for the Float decision function of track N).

The state is the exact fixed-point box (lists of corners at scale `2^-PR`).  A decision function (any function:
the Float port of box_ck14 for track N, tree data for track K) says what to do with a box: drop it, split it at the
midpoint of a coordinate, score it as a leaf, or skip it (a leaf whose float value is 0).  Only leaves contribute,
and only after an exact validity test.  The soundness proof (BHH/Tree.lean) holds for every decision function.
-/
import BHHCert.Leaf
import BHHCert.FloatBnB

namespace BHH.Cert

/-- what to do with a box -/
inductive Dec
  | drop
  | split (d : Nat)
  | leaf
  | skip
  deriving Inhabited, BEq

/-- root box corners (fixed point): `r_2 ∈ [0, k-2)`, `η_2 ∈ [0, k-2)`, others `[-(k-2), k-2)` -/
def rootLo (k : Nat) : List Int :=
  (List.range (2 * k - 3)).map fun d => if d == 0 ∨ d == 2 then 0 else -((k : Int) - 2) * ONE
def rootHi (k : Nat) : List Int :=
  (List.range (2 * k - 3)).map fun _ => ((k : Int) - 2) * ONE

/-- the exact test behind `ValidBox`: lengths, positive widths, even `lo + hi`, inside the root box -/
def validB (k : Nat) (lo hi : List Int) : Bool :=
  let m := 2 * k - 3
  lo.length == m && hi.length == m &&
  (List.range m).all fun d =>
    let a := lo.getD d 0
    let b := hi.getD d 0
    decide (a < b) && (a + b) % 2 == 0 && decide ((rootLo k).getD d 0 ≤ a) && decide (b ≤ (rootHi k).getD d 0)

/-- the exact recursion: leaves contribute `max (L lo hi) 0` if valid, splits add the two halves -/
def bnbExact (k : Nat) (dec : List Int → List Int → Dec) (L : List Int → List Int → Int) :
    Nat → List Int → List Int → Int
  | 0, _, _ => 0
  | fuel + 1, lo, hi =>
    match dec lo hi with
    | .split d =>
      if d < lo.length ∧ d < hi.length then
        let mid := (lo.getD d 0 + hi.getD d 0) / 2
        bnbExact k dec L fuel lo (hi.set d mid) + bnbExact k dec L fuel (lo.set d mid) hi
      else 0
    | .leaf => if validB k lo hi then Max.max (L lo hi) 0 else 0
    | _ => 0

/-- index of the widest coordinate (first maximum) -/
def widest (lo hi : List Int) : Nat :=
  ((List.range lo.length).foldl (fun (best : Nat × Int) d =>
    let w := hi.getD d 0 - lo.getD d 0
    if w > best.2 then (d, w) else best) (0, -1)).1

/-- the `t`-th of the `2^R` initial boxes: breadth-first bisection at the widest coordinate (box_ck14's
`initial_boxes` with `n = 2^R`); bit `R-1-i` of `t` chooses the lower (0) or upper (1) half at round `i` -/
def initBoxGo (t : Nat) : Nat → List Int → List Int → List Int × List Int
  | 0, lo, hi => (lo, hi)
  | r + 1, lo, hi =>
    let d := widest lo hi
    let mid := (lo.getD d 0 + hi.getD d 0) / 2
    if t.testBit r then initBoxGo t r (lo.set d mid) hi else initBoxGo t r lo (hi.set d mid)

def initBox (k R t : Nat) : List Int × List Int := initBoxGo t R (rootLo k) (rootHi k)

/-- the depth fuel of a tree -/
def FUEL : Nat := 400

/-- sum of the trees of the initial boxes `t ∈ [a, b)` (of `2^R`) -/
def shardSum (k : Nat) (dec : List Int → List Int → Dec) (L : List Int → List Int → Int) (R a b : Nat) : Int :=
  (List.range (b - a)).foldl (fun acc i =>
    let (lo, hi) := initBox k R (a + i)
    acc + bnbExact k dec L FUEL lo hi) 0

/-! ## the Float decision function of track N (box_ck14 port), computed from the exact corners -/

/-- exact Float of a fixed-point integer with at most 53 significant bits (else a nearby Float: decisions only) -/
def toF (n : Int) : Float :=
  let a := n.natAbs
  let s := if Nat.log2 a > 52 then Nat.log2 a - 52 else 0
  let f := Float.scaleB (Float.ofNat (a >>> s)) ((s : Int) - (PR : Int))
  if n < 0 then -f else f

open Flt in
/-- decisions of box_ck14 for the exact box (the Float images of the corners are exact) -/
def floatDec (C : Ctx) (lo hi : List Int) : Dec :=
  match Flt.decide C (lo.map toF).toArray (hi.map toF).toArray {} with
  | (.split d, _) => .split d
  | (.leaf _ flt, _) => if flt == 0 then .skip else .leaf
  | (.drop, _) => .drop

end BHH.Cert
