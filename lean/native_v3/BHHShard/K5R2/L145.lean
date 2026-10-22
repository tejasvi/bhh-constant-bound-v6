import BHH.ShardChainR2

namespace BHH.Shards

theorem k5r2_l145 : (0 : Int) ≤ BHH.Cert.shardN5r2 2375680 2392064 :=
  le_trans (le_of_eq (by norm_num)) (BHH.shardN5r2_nonneg 2375680 2392064)

end BHH.Shards
