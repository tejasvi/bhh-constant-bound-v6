import BHH.ShardChainR2

namespace BHH.Shards

theorem k5r2_l155 : (0 : Int) ≤ BHH.Cert.shardN5r2 2539520 2555904 :=
  le_trans (le_of_eq (by norm_num)) (BHH.shardN5r2_nonneg 2539520 2555904)

end BHH.Shards
