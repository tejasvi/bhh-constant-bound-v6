import BHH.ShardChainR2

namespace BHH.Shards

theorem k5r2_l061 : (0 : Int) ≤ BHH.Cert.shardN5r2 999424 1015808 :=
  le_trans (le_of_eq (by norm_num)) (BHH.shardN5r2_nonneg 999424 1015808)

end BHH.Shards
