/-
Generator of the K tree codes (untrusted, compiled): the preorder node codes of the tree that `bnbExact` walks with a
decision function (e.g. the Float decisions `floatDec ctx` of the native proof or a coarser run), packed 4 bits per node,
one Nat per initial box.  `bnbStream` with these codes walks the same tree, so `treeK k L R t (codeOf ...)` equals
`bnbExact k dec L FUEL` on the initial box `t` (checked by #eval on samples; soundness never depends on it).
-/
import BHHCert.TreeK
import BHHCert.Shard

namespace BHH.Cert

/-- preorder node codes (reversed, accumulated) of the tree walked by `bnbExact k dec L fuel lo hi` -/
def encodeGo (dec : List Int → List Int → Dec) : Nat → List Int → List Int → List Nat → List Nat
  | 0, _, _, acc => acc
  | fuel + 1, lo, hi, acc =>
    match dec lo hi with
    | .split d =>
      if d < lo.length ∧ d < hi.length then
        let mid := (lo.getD d 0 + hi.getD d 0) / 2
        let acc1 := encodeGo dec fuel lo (hi.set d mid) ((2 + d) :: acc)
        encodeGo dec fuel (lo.set d mid) hi acc1
      else (2 + d) :: acc
    | .leaf => 1 :: acc
    | _ => 0 :: acc

/-- pack node codes (each < 16), first code in the lowest 4 bits -/
def packCodes (cs : List Nat) : Nat := cs.foldr (fun c acc => acc * 16 + c) 0

/-- the code of the initial box `t` under the decision function `dec` -/
def codeOf (k : Nat) (dec : List Int → List Int → Dec) (R t : Nat) : Nat :=
  packCodes (encodeGo dec FUEL (initBox k R t).1 (initBox k R t).2 []).reverse

/-- number of nodes and leaves of a code list (diagnostics) -/
def codeStats (cs : List Nat) : Nat × Nat := (cs.length, cs.countP (· == 1))

end BHH.Cert
