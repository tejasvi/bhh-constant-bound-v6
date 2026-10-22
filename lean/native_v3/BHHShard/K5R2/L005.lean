import BHH.ShardChainR2

namespace BHH.Shards

theorem k5r2_l005 : (0 : Int) ≤ BHH.Cert.shardN5r2 81920 98304 :=
  le_trans (le_of_eq (by norm_num)) (BHH.shardN5r2_nonneg 81920 98304)

end BHH.Shards
