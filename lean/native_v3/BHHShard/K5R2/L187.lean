import BHH.ShardChainR2

namespace BHH.Shards

theorem k5r2_l187 : (0 : Int) ≤ BHH.Cert.shardN5r2 3063808 3080192 :=
  le_trans (le_of_eq (by norm_num)) (BHH.shardN5r2_nonneg 3063808 3080192)

end BHH.Shards
