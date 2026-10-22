import BHH.ShardChainR2

namespace BHH.Shards

theorem k5r2_l101 : (0 : Int) ≤ BHH.Cert.shardN5r2 1654784 1671168 :=
  le_trans (le_of_eq (by norm_num)) (BHH.shardN5r2_nonneg 1654784 1671168)

end BHH.Shards
