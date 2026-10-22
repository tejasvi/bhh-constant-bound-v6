import BHH.ShardChainR2

namespace BHH.Shards

theorem k5r2_l029 : (0 : Int) ≤ BHH.Cert.shardN5r2 475136 491520 :=
  le_trans (le_of_eq (by norm_num)) (BHH.shardN5r2_nonneg 475136 491520)

end BHH.Shards
