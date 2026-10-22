import BHH.ShardChainR2

namespace BHH.Shards

theorem k5r2_l108 : (0 : Int) ≤ BHH.Cert.shardN5r2 1769472 1785856 :=
  le_trans (le_of_eq (by norm_num)) (BHH.shardN5r2_nonneg 1769472 1785856)

end BHH.Shards
