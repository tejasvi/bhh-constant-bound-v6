import BHH.ShardChainR2

namespace BHH.Shards

theorem k5r2_l246 : (0 : Int) ≤ BHH.Cert.shardN5r2 4030464 4046848 :=
  le_trans (le_of_eq (by norm_num)) (BHH.shardN5r2_nonneg 4030464 4046848)

end BHH.Shards
