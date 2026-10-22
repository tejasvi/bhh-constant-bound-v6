import BHH.ShardChainR2

namespace BHH.Shards

theorem k5r2_l164 : (0 : Int) ≤ BHH.Cert.shardN5r2 2686976 2703360 :=
  le_trans (le_of_eq (by norm_num)) (BHH.shardN5r2_nonneg 2686976 2703360)

end BHH.Shards
