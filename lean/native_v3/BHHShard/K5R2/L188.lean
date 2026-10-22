import BHH.ShardChainR2

namespace BHH.Shards

theorem k5r2_l188 : (0 : Int) ≤ BHH.Cert.shardN5r2 3080192 3096576 :=
  le_trans (le_of_eq (by norm_num)) (BHH.shardN5r2_nonneg 3080192 3096576)

end BHH.Shards
