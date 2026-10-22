import BHH.ShardChainR2

namespace BHH.Shards

theorem k5r2_l226 : (0 : Int) ≤ BHH.Cert.shardN5r2 3702784 3719168 :=
  le_trans (le_of_eq (by norm_num)) (BHH.shardN5r2_nonneg 3702784 3719168)

end BHH.Shards
