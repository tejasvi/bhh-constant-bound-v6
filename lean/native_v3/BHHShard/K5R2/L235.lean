import BHH.ShardChainR2

namespace BHH.Shards

theorem k5r2_l235 : (0 : Int) ≤ BHH.Cert.shardN5r2 3850240 3866624 :=
  le_trans (le_of_eq (by norm_num)) (BHH.shardN5r2_nonneg 3850240 3866624)

end BHH.Shards
