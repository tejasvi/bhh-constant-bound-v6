import BHH.ShardChainR2

namespace BHH.Shards

theorem k5r2_l158 : (0 : Int) ≤ BHH.Cert.shardN5r2 2588672 2605056 :=
  le_trans (le_of_eq (by norm_num)) (BHH.shardN5r2_nonneg 2588672 2605056)

end BHH.Shards
