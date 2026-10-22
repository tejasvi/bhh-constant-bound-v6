import BHH.ShardChainR2

namespace BHH.Shards

theorem k5r2_l013 : (0 : Int) ≤ BHH.Cert.shardN5r2 212992 229376 :=
  le_trans (le_of_eq (by norm_num)) (BHH.shardN5r2_nonneg 212992 229376)

end BHH.Shards
