/-
Track K: the bisection tree driven by data instead of Float decisions (core Lean, kernel-friendly).

A tree is read in preorder from a stream of node codes: `0` drop (or skip), `1` leaf, `2 + d` split at the midpoint of
coordinate `d` (lower half first).  `bnbStream` works for any stream (`read : S → Nat × S`); `read4` reads 4-bit codes
from a Nat (least significant first), so that one Nat literal per initial box describes its tree.  The soundness
theorem (BHH/TreeK.lean) holds for every stream, like `bnbExact_sound` for every decision function.
-/
import BHHCert.Tree

namespace BHH.Cert

/-- the bisection recursion driven by a stream of node codes; returns the value and the rest of the stream -/
def bnbStream {S : Type} (k : Nat) (L : List Int → List Int → Int) (read : S → Nat × S) :
    Nat → S → List Int → List Int → Int × S
  | 0, s, _, _ => (0, s)
  | fuel + 1, s, lo, hi =>
    let c := (read s).1
    let s1 := (read s).2
    if c = 1 then ((if validB k lo hi then Max.max (L lo hi) 0 else 0), s1)
    else if 2 ≤ c then
      let d := c - 2
      if d < lo.length ∧ d < hi.length then
        let mid := (lo.getD d 0 + hi.getD d 0) / 2
        let r1 := bnbStream k L read fuel s1 lo (hi.set d mid)
        let r2 := bnbStream k L read fuel r1.2 (lo.set d mid) hi
        (r1.1 + r2.1, r2.2)
      else (0, s1)
    else (0, s1)

/-- read a 4-bit node code (least significant bits first) -/
def read4 (c : Nat) : Nat × Nat := (c % 16, c >>> 4)

/-- the tree of the initial box `t` (of `2^R`), described by the code `c` -/
def treeK (k : Nat) (L : List Int → List Int → Int) (R t c : Nat) : Int :=
  (bnbStream k L read4 FUEL c (initBox k R t).1 (initBox k R t).2).1

/-- sum of the trees of the initial boxes `a, a+1, ..., a + codes.length - 1`, with their codes -/
def shardSumK (k : Nat) (L : List Int → List Int → Int) (R a : Nat) : List Nat → Int
  | [] => 0
  | c :: cs => treeK k L R a c + shardSumK k L R (a + 1) cs

end BHH.Cert
