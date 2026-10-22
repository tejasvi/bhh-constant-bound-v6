import BHH.ShardChainR2

namespace BHH.Shards

theorem k5r2_l060 : (0 : Int) ≤ BHH.Cert.shardN5r2 983040 999424 :=
  le_trans (le_of_eq (by norm_num)) (BHH.shardN5r2_nonneg 983040 999424)

end BHH.Shards
