import BHH.ShardChainR2

namespace BHH.Shards

theorem k5r2_l081 : (0 : Int) ≤ BHH.Cert.shardN5r2 1327104 1343488 :=
  le_trans (le_of_eq (by norm_num)) (BHH.shardN5r2_nonneg 1327104 1343488)

end BHH.Shards
