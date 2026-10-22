import BHH.ShardChainR2

namespace BHH.Shards

theorem k5r2_l149 : (0 : Int) ≤ BHH.Cert.shardN5r2 2441216 2457600 :=
  le_trans (le_of_eq (by norm_num)) (BHH.shardN5r2_nonneg 2441216 2457600)

end BHH.Shards
