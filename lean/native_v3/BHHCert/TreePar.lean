/-
Parallel evaluation of the bisection tree for the N track (core Lean).  `bnbPar` is `bnbExact` with the two halves of
every split above depth `pd` evaluated by `Task.spawn` (a separate thread in compiled code).  Since
`(Task.spawn f).get = f ()` by definition, `bnbPar = bnbExact` (BHH/TreePar.lean), so a shard theorem about `shardN`
can be proved by rewriting to `shardNPar` and running `native_decide` on many threads.
-/
import BHHCert.Shard

namespace BHH.Cert

/-- `bnbExact` with the splits above depth `pd` evaluated in parallel -/
def bnbPar (k : Nat) (dec : List Int → List Int → Dec) (L : List Int → List Int → Int) :
    Nat → Nat → List Int → List Int → Int
  | 0, fuel, lo, hi => bnbExact k dec L fuel lo hi
  | _ + 1, 0, _, _ => 0
  | pd + 1, fuel + 1, lo, hi =>
    match dec lo hi with
    | .split d =>
      if d < lo.length ∧ d < hi.length then
        let mid := (lo.getD d 0 + hi.getD d 0) / 2
        let t1 := Task.spawn fun _ => bnbPar k dec L pd fuel lo (hi.set d mid)
        let v2 := bnbPar k dec L pd fuel (lo.set d mid) hi
        t1.get + v2
      else 0
    | .leaf => if validB k lo hi then Max.max (L lo hi) 0 else 0
    | _ => 0

/-- the shard sum with every initial box's tree evaluated by `bnbPar` (boxes in parallel too) -/
def shardSumPar (k : Nat) (dec : List Int → List Int → Dec) (L : List Int → List Int → Int) (pd R a b : Nat) : Int :=
  let ts := (List.range (b - a)).map fun i =>
    Task.spawn fun _ => bnbPar k dec L pd FUEL (initBox k R (a + i)).1 (initBox k R (a + i)).2
  ts.foldl (fun acc t => acc + t.get) 0

/-- the N-track shard sum, evaluated in parallel -/
def shardNPar (k pd a b : Nat) : Int := shardSumPar k (floatDec (ctxN k)) (Lk k) pd (RN k) a b

end BHH.Cert
