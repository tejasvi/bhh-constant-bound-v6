import BHH.ShardChainR2

namespace BHH.Shards

theorem k5r2_l182 : (0 : Int) ≤ BHH.Cert.shardN5r2 2981888 2998272 :=
  le_trans (le_of_eq (by norm_num)) (BHH.shardN5r2_nonneg 2981888 2998272)

end BHH.Shards
