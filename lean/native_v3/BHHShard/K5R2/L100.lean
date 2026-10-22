import BHH.ShardChainR2

namespace BHH.Shards

theorem k5r2_l100 : (0 : Int) ≤ BHH.Cert.shardN5r2 1638400 1654784 :=
  le_trans (le_of_eq (by norm_num)) (BHH.shardN5r2_nonneg 1638400 1654784)

end BHH.Shards
