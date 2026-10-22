import BHH.ShardChainR2

namespace BHH.Shards

theorem k5r2_l172 : (0 : Int) ≤ BHH.Cert.shardN5r2 2818048 2834432 :=
  le_trans (le_of_eq (by norm_num)) (BHH.shardN5r2_nonneg 2818048 2834432)

end BHH.Shards
