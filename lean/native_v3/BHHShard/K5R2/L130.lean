import BHH.ShardChainR2

namespace BHH.Shards

theorem k5r2_l130 : (0 : Int) ≤ BHH.Cert.shardN5r2 2129920 2146304 :=
  le_trans (le_of_eq (by norm_num)) (BHH.shardN5r2_nonneg 2129920 2146304)

end BHH.Shards
