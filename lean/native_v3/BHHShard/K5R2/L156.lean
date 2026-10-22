import BHH.ShardChainR2

namespace BHH.Shards

theorem k5r2_l156 : (0 : Int) ≤ BHH.Cert.shardN5r2 2555904 2572288 :=
  le_trans (le_of_eq (by norm_num)) (BHH.shardN5r2_nonneg 2555904 2572288)

end BHH.Shards
