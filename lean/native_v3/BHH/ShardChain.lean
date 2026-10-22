/-
Combinators for the N-track shard theorems (generated modules BHHShard/K*/G*.lean, All.lean): adjacent shard ranges add,
and every shard sum is nonnegative (the ranges whose C value is 0 are covered without computation).
-/
import BHH.Tree
import BHH.TreePar
import BHHCert.Shard

namespace BHH

open BHH.Cert

theorem shardN_add_le {k a b c : ℕ} {v w : ℤ} (hab : a ≤ b) (hbc : b ≤ c)
    (h : v ≤ shardN k a b) (h' : w ≤ shardN k b c) : v + w ≤ shardN k a c := by
  unfold shardN at *
  rw [← shardSum_add k _ _ hab hbc]
  exact add_le_add h h'

theorem shardN_nonneg (k a b : ℕ) : (0 : ℤ) ≤ shardN k a b := shardSum_nonneg k _ _ _ a b

theorem le_shardN_of_par {k pd a b : ℕ} {v : ℤ} (h : v ≤ shardNPar k pd a b) : v ≤ shardN k a b :=
  shardNPar_eq k pd a b ▸ h

end BHH
