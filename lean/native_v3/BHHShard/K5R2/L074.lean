import BHH.ShardChainR2

namespace BHH.Shards

theorem k5r2_l074 : (0 : Int) ≤ BHH.Cert.shardN5r2 1212416 1228800 :=
  le_trans (le_of_eq (by norm_num)) (BHH.shardN5r2_nonneg 1212416 1228800)

end BHH.Shards
