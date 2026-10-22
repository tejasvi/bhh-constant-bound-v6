import BHH.ShardChainR2

namespace BHH.Shards

theorem k5r2_l144 : (0 : Int) ≤ BHH.Cert.shardN5r2 2359296 2375680 :=
  le_trans (le_of_eq (by norm_num)) (BHH.shardN5r2_nonneg 2359296 2375680)

end BHH.Shards
