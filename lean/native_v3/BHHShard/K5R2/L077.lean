import BHH.ShardChainR2

namespace BHH.Shards

theorem k5r2_l077 : (0 : Int) ≤ BHH.Cert.shardN5r2 1261568 1277952 :=
  le_trans (le_of_eq (by norm_num)) (BHH.shardN5r2_nonneg 1261568 1277952)

end BHH.Shards
