import BHH.ShardChainR2

namespace BHH.Shards

theorem k5r2_l146 : (0 : Int) ≤ BHH.Cert.shardN5r2 2392064 2408448 :=
  le_trans (le_of_eq (by norm_num)) (BHH.shardN5r2_nonneg 2392064 2408448)

end BHH.Shards
