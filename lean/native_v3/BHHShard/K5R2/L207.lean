import BHH.ShardChainR2

namespace BHH.Shards

theorem k5r2_l207 : (0 : Int) ≤ BHH.Cert.shardN5r2 3391488 3407872 :=
  le_trans (le_of_eq (by norm_num)) (BHH.shardN5r2_nonneg 3391488 3407872)

end BHH.Shards
