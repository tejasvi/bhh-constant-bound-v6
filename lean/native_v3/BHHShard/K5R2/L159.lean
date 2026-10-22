import BHH.ShardChainR2

namespace BHH.Shards

theorem k5r2_l159 : (0 : Int) ≤ BHH.Cert.shardN5r2 2605056 2621440 :=
  le_trans (le_of_eq (by norm_num)) (BHH.shardN5r2_nonneg 2605056 2621440)

end BHH.Shards
