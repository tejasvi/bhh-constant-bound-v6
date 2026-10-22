import BHH.ShardChainR2

namespace BHH.Shards

theorem k5r2_l014 : (0 : Int) ≤ BHH.Cert.shardN5r2 229376 245760 :=
  le_trans (le_of_eq (by norm_num)) (BHH.shardN5r2_nonneg 229376 245760)

end BHH.Shards
