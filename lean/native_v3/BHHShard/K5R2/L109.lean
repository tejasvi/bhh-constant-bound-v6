import BHH.ShardChainR2

namespace BHH.Shards

theorem k5r2_l109 : (0 : Int) ≤ BHH.Cert.shardN5r2 1785856 1802240 :=
  le_trans (le_of_eq (by norm_num)) (BHH.shardN5r2_nonneg 1785856 1802240)

end BHH.Shards
