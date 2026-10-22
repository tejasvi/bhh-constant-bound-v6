import BHH.ShardChainR2

namespace BHH.Shards

theorem k5r2_l076 : (0 : Int) ≤ BHH.Cert.shardN5r2 1245184 1261568 :=
  le_trans (le_of_eq (by norm_num)) (BHH.shardN5r2_nonneg 1245184 1261568)

end BHH.Shards
