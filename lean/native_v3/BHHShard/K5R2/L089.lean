import BHH.ShardChainR2

namespace BHH.Shards

theorem k5r2_l089 : (0 : Int) ≤ BHH.Cert.shardN5r2 1458176 1474560 :=
  le_trans (le_of_eq (by norm_num)) (BHH.shardN5r2_nonneg 1458176 1474560)

end BHH.Shards
