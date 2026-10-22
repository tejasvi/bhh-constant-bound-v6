import BHH.ShardChainR2

namespace BHH.Shards

theorem k5r2_l223 : (0 : Int) ≤ BHH.Cert.shardN5r2 3653632 3670016 :=
  le_trans (le_of_eq (by norm_num)) (BHH.shardN5r2_nonneg 3653632 3670016)

end BHH.Shards
