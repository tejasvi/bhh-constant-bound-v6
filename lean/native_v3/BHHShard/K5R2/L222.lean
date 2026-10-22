import BHH.ShardChainR2

namespace BHH.Shards

theorem k5r2_l222 : (0 : Int) ≤ BHH.Cert.shardN5r2 3637248 3653632 :=
  le_trans (le_of_eq (by norm_num)) (BHH.shardN5r2_nonneg 3637248 3653632)

end BHH.Shards
