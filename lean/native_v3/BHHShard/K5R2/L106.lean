import BHH.ShardChainR2

namespace BHH.Shards

theorem k5r2_l106 : (0 : Int) ≤ BHH.Cert.shardN5r2 1736704 1753088 :=
  le_trans (le_of_eq (by norm_num)) (BHH.shardN5r2_nonneg 1736704 1753088)

end BHH.Shards
