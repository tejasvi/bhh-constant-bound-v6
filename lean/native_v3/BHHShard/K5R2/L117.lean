import BHH.ShardChainR2

namespace BHH.Shards

theorem k5r2_l117 : (0 : Int) ≤ BHH.Cert.shardN5r2 1916928 1933312 :=
  le_trans (le_of_eq (by norm_num)) (BHH.shardN5r2_nonneg 1916928 1933312)

end BHH.Shards
