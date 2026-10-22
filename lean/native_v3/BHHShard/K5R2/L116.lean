import BHH.ShardChainR2

namespace BHH.Shards

theorem k5r2_l116 : (0 : Int) ≤ BHH.Cert.shardN5r2 1900544 1916928 :=
  le_trans (le_of_eq (by norm_num)) (BHH.shardN5r2_nonneg 1900544 1916928)

end BHH.Shards
