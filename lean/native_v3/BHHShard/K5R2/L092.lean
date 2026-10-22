import BHH.ShardChainR2

namespace BHH.Shards

theorem k5r2_l092 : (0 : Int) ≤ BHH.Cert.shardN5r2 1507328 1523712 :=
  le_trans (le_of_eq (by norm_num)) (BHH.shardN5r2_nonneg 1507328 1523712)

end BHH.Shards
