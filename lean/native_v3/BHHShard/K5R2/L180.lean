import BHH.ShardChainR2

namespace BHH.Shards

theorem k5r2_l180 : (0 : Int) ≤ BHH.Cert.shardN5r2 2949120 2965504 :=
  le_trans (le_of_eq (by norm_num)) (BHH.shardN5r2_nonneg 2949120 2965504)

end BHH.Shards
