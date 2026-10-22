/-
`bnbPar = bnbExact` and `shardNPar = shardN` (BHHCert/TreePar.lean): the parallel evaluation computes the same value,
because `(Task.spawn f).get = f ()` by definition.  Used by the N shard theorems of heavy initial boxes:
`(v : Int) ≤ shardN k a b` is proved by rewriting with `shardNPar_eq` and `native_decide` on `shardNPar`.
-/
import BHH.Tree
import BHHCert.TreePar

namespace BHH.E

open BHH.Cert

theorem bnbPar_eq (k : ℕ) (dec : List ℤ → List ℤ → Dec) (L : List ℤ → List ℤ → ℤ) :
    ∀ pd fuel lo hi, bnbPar k dec L pd fuel lo hi = bnbExact k dec L fuel lo hi
  | 0, fuel, lo, hi => by simp [bnbPar]
  | pd + 1, 0, lo, hi => by simp [bnbPar, bnbExact]
  | pd + 1, fuel + 1, lo, hi => by
    rw [bnbPar, bnbExact]
    cases h : dec lo hi with
    | split d =>
      simp only []
      split_ifs
      · simp only [Task.spawn, bnbPar_eq k dec L pd fuel]
      · rfl
    | leaf => rfl
    | drop => rfl
    | skip => rfl

theorem shardSumPar_eq (k : ℕ) (dec : List ℤ → List ℤ → Dec) (L : List ℤ → List ℤ → ℤ) (pd R a b : ℕ) :
    shardSumPar k dec L pd R a b = shardSum k dec L R a b := by
  unfold shardSumPar shardSum
  rw [List.foldl_map]
  congr 1
  funext acc i
  simp only [Task.spawn, bnbPar_eq]

theorem shardNPar_eq (k pd a b : ℕ) : shardNPar k pd a b = shardN k a b := by
  unfold shardNPar shardN
  exact shardSumPar_eq k _ _ pd _ a b

end BHH.E

namespace BHH

export E (bnbPar_eq shardSumPar_eq shardNPar_eq)

end BHH
