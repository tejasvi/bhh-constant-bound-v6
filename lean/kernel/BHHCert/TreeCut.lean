/-
Track K sub-box shards (core Lean, kernel-friendly): a bisection tree whose external nodes are evaluated by separate
kernel theorems.

`bnbCut` reads a tree in preorder like `bnbStream`, with one more node code: `15` is an external node, whose value is
the next element of the list `ext` (consumed in preorder; `0` once `ext` is used up).  `cutBoxes` lists the boxes at the
external nodes, in the same order, without evaluating any leaf.  An external entry is `(v, code, lo, hi)`: the claim
`v ≤ (bnbStream k L read4 FUEL code lo hi).1` for the tree `code` on the box `[lo, hi]`, checked by `subOK` on a list of
entries.  `cutOK` checks that the boxes of the entries are the external boxes of the cut tree and that `V` is at most its
value with the claimed external values.  The soundness theorems (BHH/TreeCut.lean) hold for every stream and every list
of entries.
-/
import BHHCert.TreeK

namespace BHH.Cert

/-- an external entry: claimed value, tree code, box corners -/
abbrev ExtEntry := Int × Nat × List Int × List Int

/-- the bisection recursion with external nodes (code `15`): returns the value, the rest of the stream and the rest of
the external values -/
def bnbCut {S : Type} (k : Nat) (L : List Int → List Int → Int) (read : S → Nat × S) :
    Nat → S → List Int → List Int → List Int → Int × S × List Int
  | 0, s, _, _, ext => (0, s, ext)
  | fuel + 1, s, lo, hi, ext =>
    let c := (read s).1
    let s1 := (read s).2
    if c = 1 then ((if validB k lo hi then Max.max (L lo hi) 0 else 0), s1, ext)
    else if c = 15 then (ext.headD 0, s1, ext.tail)
    else if 2 ≤ c then
      let d := c - 2
      if d < lo.length ∧ d < hi.length then
        let mid := (lo.getD d 0 + hi.getD d 0) / 2
        let r1 := bnbCut k L read fuel s1 lo (hi.set d mid) ext
        let r2 := bnbCut k L read fuel r1.2.1 (lo.set d mid) hi r1.2.2
        (r1.1 + r2.1, r2.2.1, r2.2.2)
      else (0, s1, ext)
    else (0, s1, ext)

/-- the boxes at the external nodes of the tree, in preorder, and the rest of the stream -/
def cutBoxes {S : Type} (read : S → Nat × S) : Nat → S → List Int → List Int → List (List Int × List Int) × S
  | 0, s, _, _ => ([], s)
  | fuel + 1, s, lo, hi =>
    let c := (read s).1
    let s1 := (read s).2
    if c = 1 then ([], s1)
    else if c = 15 then ([(lo, hi)], s1)
    else if 2 ≤ c then
      let d := c - 2
      if d < lo.length ∧ d < hi.length then
        let mid := (lo.getD d 0 + hi.getD d 0) / 2
        let r1 := cutBoxes read fuel s1 lo (hi.set d mid)
        let r2 := cutBoxes read fuel r1.2 (lo.set d mid) hi
        (r1.1 ++ r2.1, r2.2)
      else ([], s1)
    else ([], s1)

/-- the box of an external entry -/
def ExtEntry.box (x : ExtEntry) : List Int × List Int := (x.2.2.1, x.2.2.2)

/-- the claim of one external entry: its value is at most the tree value on its box -/
def extOK (k : Nat) (L : List Int → List Int → Int) (x : ExtEntry) : Bool :=
  decide (x.1 ≤ (bnbStream k L read4 FUEL x.2.1 x.2.2.1 x.2.2.2).1)

/-- the claims of a list of external entries -/
def subOK (k : Nat) (L : List Int → List Int → Int) (X : List ExtEntry) : Bool := X.all (extOK k L)

/-- the cut tree `c` on `[lo, hi]` with the external entries `X` (in preorder) has value at least `V` -/
def cutOK (k : Nat) (L : List Int → List Int → Int) (c : Nat) (lo hi : List Int) (X : List ExtEntry) (V : Int) :
    Bool :=
  decide ((cutBoxes read4 FUEL c lo hi).1 = X.map ExtEntry.box) &&
    decide (V ≤ (bnbCut k L read4 FUEL c lo hi (X.map (·.1))).1)

end BHH.Cert
