/-
Track N only: the g tables `gtN k` named by the shard theorems are sound, by `native_decide` on the table check
`checkTab` (whose soundness, `checkTab_sound`, is kernel-proved in `BHH/Graph.lean`).  This is the only file of
module E that uses `native_decide` (axiom `Lean.ofReduceBool`).
-/
import BHH.Graph
import BHHCert.Shard

namespace BHH.E

open BHH.Cert

theorem gtN_check_three : checkTab 3 (gtN 3).gmin = true := by native_decide

theorem gtN_check_four : checkTab 4 (gtN 4).gmin = true := by native_decide

theorem gtN_check_five : checkTab 5 (gtN 5).gmin = true := by native_decide

theorem gtN_sound_three : GTabSound 3 (gtN 3) := checkTab_sound (by norm_num) (gtN 3) gtN_check_three

theorem gtN_sound_four : GTabSound 4 (gtN 4) := checkTab_sound (by norm_num) (gtN 4) gtN_check_four

theorem gtN_sound_five : GTabSound 5 (gtN 5) := checkTab_sound (by norm_num) (gtN 5) gtN_check_five

theorem gtN_nonneg_three : ∀ idx, idx < 3 ^ (pairList 3).length → 0 ≤ (gtN 3).gmin idx := by native_decide

theorem gtN_nonneg_four : ∀ idx, idx < 3 ^ (pairList 4).length → 0 ≤ (gtN 4).gmin idx := by native_decide

theorem gtN_nonneg_five : ∀ idx, idx < 3 ^ (pairList 5).length → 0 ≤ (gtN 5).gmin idx := by native_decide

/-- the N-track tables are nonnegative (`g ≥ 0`), as module D needs for the extra term of Prop 3.6 -/
theorem gtN_nonneg : ∀ k ∈ ({3, 4, 5} : Finset ℕ), ∀ idx, idx < 3 ^ (pairList k).length → 0 ≤ (gtN k).gmin idx := by
  intro k hk
  simp only [Finset.mem_insert, Finset.mem_singleton] at hk
  rcases hk with rfl | rfl | rfl
  · exact gtN_nonneg_three
  · exact gtN_nonneg_four
  · exact gtN_nonneg_five

end BHH.E

namespace BHH

-- the deliverables of this file, also under `BHH` (helpers stay in `BHH.E`)
export E (gtN_check_three gtN_check_four gtN_check_five gtN_sound_three gtN_sound_four gtN_sound_five
  gtN_nonneg_three gtN_nonneg_four gtN_nonneg_five gtN_nonneg)

end BHH
