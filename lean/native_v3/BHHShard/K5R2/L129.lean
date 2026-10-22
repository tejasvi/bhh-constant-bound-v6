import BHH.ShardChainR2

namespace BHH.Shards

theorem k5r2_l129 : (0 : Int) ≤ BHH.Cert.shardN5r2 2113536 2129920 :=
  le_trans (le_of_eq (by norm_num)) (BHH.shardN5r2_nonneg 2113536 2129920)

end BHH.Shards
