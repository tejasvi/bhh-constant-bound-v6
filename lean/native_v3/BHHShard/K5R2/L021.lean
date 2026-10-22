import BHH.ShardChainR2

namespace BHH.Shards

theorem k5r2_l021 : (0 : Int) ≤ BHH.Cert.shardN5r2 344064 360448 :=
  le_trans (le_of_eq (by norm_num)) (BHH.shardN5r2_nonneg 344064 360448)

end BHH.Shards
