import BHH.ShardChainR2

namespace BHH.Shards

theorem k5r2_l196 : (0 : Int) ≤ BHH.Cert.shardN5r2 3211264 3227648 :=
  le_trans (le_of_eq (by norm_num)) (BHH.shardN5r2_nonneg 3211264 3227648)

end BHH.Shards
