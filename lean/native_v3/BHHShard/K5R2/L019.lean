import BHH.ShardChainR2

namespace BHH.Shards

theorem k5r2_l019 : (0 : Int) ≤ BHH.Cert.shardN5r2 311296 327680 :=
  le_trans (le_of_eq (by norm_num)) (BHH.shardN5r2_nonneg 311296 327680)

end BHH.Shards
