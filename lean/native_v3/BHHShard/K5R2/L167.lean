import BHH.ShardChainR2

namespace BHH.Shards

theorem k5r2_l167 : (0 : Int) ≤ BHH.Cert.shardN5r2 2736128 2752512 :=
  le_trans (le_of_eq (by norm_num)) (BHH.shardN5r2_nonneg 2736128 2752512)

end BHH.Shards
