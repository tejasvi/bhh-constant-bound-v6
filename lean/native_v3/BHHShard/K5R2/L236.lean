import BHH.ShardChainR2

namespace BHH.Shards

theorem k5r2_l236 : (0 : Int) ≤ BHH.Cert.shardN5r2 3866624 3883008 :=
  le_trans (le_of_eq (by norm_num)) (BHH.shardN5r2_nonneg 3866624 3883008)

end BHH.Shards
