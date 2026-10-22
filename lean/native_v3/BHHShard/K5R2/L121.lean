import BHH.ShardChainR2

namespace BHH.Shards

theorem k5r2_l121 : (0 : Int) ≤ BHH.Cert.shardN5r2 1982464 1998848 :=
  le_trans (le_of_eq (by norm_num)) (BHH.shardN5r2_nonneg 1982464 1998848)

end BHH.Shards
