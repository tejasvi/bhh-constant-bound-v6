import BHH.ShardChainR2

namespace BHH.Shards

theorem k5r2_l186 : (0 : Int) ≤ BHH.Cert.shardN5r2 3047424 3063808 :=
  le_trans (le_of_eq (by norm_num)) (BHH.shardN5r2_nonneg 3047424 3063808)

end BHH.Shards
