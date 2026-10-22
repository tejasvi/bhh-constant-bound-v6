import BHH.ShardChainR2

namespace BHH.Shards

theorem k5r2_l204 : (0 : Int) ≤ BHH.Cert.shardN5r2 3342336 3358720 :=
  le_trans (le_of_eq (by norm_num)) (BHH.shardN5r2_nonneg 3342336 3358720)

end BHH.Shards
