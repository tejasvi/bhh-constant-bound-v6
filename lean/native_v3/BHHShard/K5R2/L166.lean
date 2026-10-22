import BHH.ShardChainR2

namespace BHH.Shards

theorem k5r2_l166 : (0 : Int) ≤ BHH.Cert.shardN5r2 2719744 2736128 :=
  le_trans (le_of_eq (by norm_num)) (BHH.shardN5r2_nonneg 2719744 2736128)

end BHH.Shards
