/-
Native proof, refined C5 run: the shard theorems `(v : Int) ≤ shardN5r2Par pd a b` (BHHCert/ShardR2.lean) give bounds for
`shardN5r2`, consecutive ranges add up, and the sum over all initial boxes bounds `C_5`.
-/
import BHH.MainV2
import BHH.TreePar
import BHHCert.ShardR2

namespace BHH

open BHH.Cert

theorem shardN5r2Par_eq (pd a b : ℕ) : shardN5r2Par pd a b = shardN5r2 a b := by
  unfold shardN5r2Par shardN5r2
  exact E.shardSumPar_eq 5 _ _ pd _ a b

theorem le_shardN5r2_of_par {pd a b : ℕ} {v : ℤ} (h : v ≤ shardN5r2Par pd a b) : v ≤ shardN5r2 a b :=
  shardN5r2Par_eq pd a b ▸ h

theorem shardN5r2_add_le {a b c : ℕ} {v w : ℤ} (hab : a ≤ b) (hbc : b ≤ c)
    (h : v ≤ shardN5r2 a b) (h' : w ≤ shardN5r2 b c) : v + w ≤ shardN5r2 a c := by
  unfold shardN5r2 at *
  rw [← shardSum_add 5 _ _ hab hbc]
  exact add_le_add h h'

theorem shardN5r2_nonneg (a b : ℕ) : (0 : ℤ) ≤ shardN5r2 a b := shardSum_nonneg 5 _ _ _ a b

/-- `C_5` from the refined C5 shard sum over all initial boxes -/
theorem C5_ge_of_shardN5r2 (hL : LeafSoundProp 5 (Lk 5)) {S : ℤ} (hS : S ≤ shardN5r2 0 (2 ^ RN 5)) {t : ℝ}
    (ht : t ≤ 21 / 32 * piThreeHalvesLo / 2 * ((S : ℝ) / 2 ^ OS)) : ENNReal.ofReal t ≤ C 5 := by
  have hp := E.piThreeHalvesLo_nonneg
  exact C_ge_of_shardSum (by norm_num) hL _ le_rfl hS (by positivity) E.kappa_five_gt.le ht

end BHH
