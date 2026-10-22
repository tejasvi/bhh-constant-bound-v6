import BHH.ShardChainR2

namespace BHH.Shards

theorem k5r2_l017 : (0 : Int) ≤ BHH.Cert.shardN5r2 278528 294912 :=
  le_trans (le_of_eq (by norm_num)) (BHH.shardN5r2_nonneg 278528 294912)

end BHH.Shards
