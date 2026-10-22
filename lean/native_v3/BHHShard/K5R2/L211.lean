import BHH.ShardChainR2

namespace BHH.Shards

theorem k5r2_l211 : (0 : Int) ≤ BHH.Cert.shardN5r2 3457024 3473408 :=
  le_trans (le_of_eq (by norm_num)) (BHH.shardN5r2_nonneg 3457024 3473408)

end BHH.Shards
