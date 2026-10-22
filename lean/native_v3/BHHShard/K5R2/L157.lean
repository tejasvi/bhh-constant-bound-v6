import BHH.ShardChainR2

namespace BHH.Shards

theorem k5r2_l157 : (0 : Int) ≤ BHH.Cert.shardN5r2 2572288 2588672 :=
  le_trans (le_of_eq (by norm_num)) (BHH.shardN5r2_nonneg 2572288 2588672)

end BHH.Shards
