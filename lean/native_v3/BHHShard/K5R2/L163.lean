import BHH.ShardChainR2

namespace BHH.Shards

theorem k5r2_l163 : (0 : Int) ≤ BHH.Cert.shardN5r2 2670592 2686976 :=
  le_trans (le_of_eq (by norm_num)) (BHH.shardN5r2_nonneg 2670592 2686976)

end BHH.Shards
