/-
`MainBoundsV3` (Theorem 1.1 of the paper; `C_5` from the refined C5 run) from leaf soundness (module D) and the
shard bounds of the native proof: `C_3`, `C_4` as in `mainBoundsV2_of`, `C_5` from `shardN5r2` (BHH/ShardChainR2.lean).
-/
import BHH.MainV2
import BHH.ShardChainR2
import BHH.StatementW3

namespace BHH.E

open BHH.Cert

theorem mainBoundsV3_of
    (hL : GreenFormula → VertexLemmaSeg → ∀ k : ℕ, 3 ≤ k → k ≤ 5 → LeafSoundProp k (Lk k))
    {S3 S4 S5 : ℤ} (h3 : S3 ≤ shardN 3 0 (2 ^ RN 3)) (h4 : S4 ≤ shardN 4 0 (2 ^ RN 4))
    (h5 : S5 ≤ shardN5r2 0 (2 ^ RN 5))
    (c3 : (117130195 / 10 ^ 10 : ℝ) ≤ 1 / 4 * piThreeHalvesLo / 2 * ((S3 : ℝ) / 2 ^ OS))
    (c4 : (63707166 / 10 ^ 10 : ℝ) ≤ 5 / 16 * piThreeHalvesLo / 2 * ((S4 : ℝ) / 2 ^ OS))
    (c5 : (35280362 / 10 ^ 10 : ℝ) ≤ 21 / 32 * piThreeHalvesLo / 2 * ((S5 : ℝ) / 2 ^ OS)) :
    MainBoundsV3 := by
  intro hG hV
  have hp := piThreeHalvesLo_nonneg
  refine ⟨?_, ?_, ?_⟩
  · exact C_ge_of_shardN (by norm_num) (hL hG hV 3 le_rfl (by norm_num)) h3 (by positivity)
      kappa_three_gt.le c3
  · exact C_ge_of_shardN (by norm_num) (hL hG hV 4 (by norm_num) (by norm_num)) h4 (by positivity)
      kappa_four_gt.le c4
  · exact C5_ge_of_shardN5r2 (hL hG hV 5 (by norm_num) le_rfl) h5 c5

end BHH.E

namespace BHH

-- the deliverable of this file, also under `BHH`
export E (mainBoundsV3_of)

end BHH
