import BHH.ShardChainR2

namespace BHH.Shards

theorem k5r2_l232 : (0 : Int) ≤ BHH.Cert.shardN5r2 3801088 3817472 :=
  le_trans (le_of_eq (by norm_num)) (BHH.shardN5r2_nonneg 3801088 3817472)

end BHH.Shards
