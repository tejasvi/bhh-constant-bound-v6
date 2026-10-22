/-
The g tables of track N are nonnegative (finite checks by native_decide; `2g ≥ 0` for every graph, and the tables
are minima over completions).
-/
import BHHCert.Shard
import BHH.Interfaces

open BHH.Cert

namespace BHH

lemma all_range_imp_D {n : ℕ} {p : ℕ → Bool} (h : (List.range n).all p = true) : ∀ i, i < n → p i = true := by
  intro i hi
  exact List.all_eq_true.mp h i (List.mem_range.mpr hi)

theorem gtN_nonneg_D3 : (List.range (3 ^ (pairList 3).length)).all (fun idx => decide (0 ≤ (gtN 3).gmin idx)) = true := by
  native_decide
theorem gtN_nonneg_D4 : (List.range (3 ^ (pairList 4).length)).all (fun idx => decide (0 ≤ (gtN 4).gmin idx)) = true := by
  native_decide
theorem gtN_nonneg_D5 : (List.range (3 ^ (pairList 5).length)).all (fun idx => decide (0 ≤ (gtN 5).gmin idx)) = true := by
  native_decide

theorem gtN_nonneg_D : ∀ k, 3 ≤ k → k ≤ 5 → ∀ idx, idx < 3 ^ (pairList k).length → 0 ≤ (gtN k).gmin idx := by
  intro k hk3 hk5 idx hidx
  interval_cases k
  · simpa using all_range_imp_D gtN_nonneg_D3 idx hidx
  · simpa using all_range_imp_D gtN_nonneg_D4 idx hidx
  · simpa using all_range_imp_D gtN_nonneg_D5 idx hidx

end BHH
