import BHH.ShardChainR2

namespace BHH.Shards

theorem k5r2_l197 : (0 : Int) ≤ BHH.Cert.shardN5r2 3227648 3244032 :=
  le_trans (le_of_eq (by norm_num)) (BHH.shardN5r2_nonneg 3227648 3244032)

end BHH.Shards
