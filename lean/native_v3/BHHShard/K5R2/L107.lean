import BHH.ShardChainR2

namespace BHH.Shards

theorem k5r2_l107 : (0 : Int) ≤ BHH.Cert.shardN5r2 1753088 1769472 :=
  le_trans (le_of_eq (by norm_num)) (BHH.shardN5r2_nonneg 1753088 1769472)

end BHH.Shards
