import BHH.ShardChainR2

namespace BHH.Shards

theorem k5r2_l199 : (0 : Int) ≤ BHH.Cert.shardN5r2 3260416 3276800 :=
  le_trans (le_of_eq (by norm_num)) (BHH.shardN5r2_nonneg 3260416 3276800)

end BHH.Shards
