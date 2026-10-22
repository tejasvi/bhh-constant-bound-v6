import BHH.ShardChainR2

namespace BHH.Shards

theorem k5r2_l215 : (0 : Int) ≤ BHH.Cert.shardN5r2 3522560 3538944 :=
  le_trans (le_of_eq (by norm_num)) (BHH.shardN5r2_nonneg 3522560 3538944)

end BHH.Shards
