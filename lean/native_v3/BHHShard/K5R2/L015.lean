import BHH.ShardChainR2

namespace BHH.Shards

theorem k5r2_l015 : (0 : Int) ≤ BHH.Cert.shardN5r2 245760 262144 :=
  le_trans (le_of_eq (by norm_num)) (BHH.shardN5r2_nonneg 245760 262144)

end BHH.Shards
