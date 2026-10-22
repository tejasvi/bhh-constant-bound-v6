import BHH.ShardChainR2

namespace BHH.Shards

theorem k5r2_l075 : (0 : Int) ≤ BHH.Cert.shardN5r2 1228800 1245184 :=
  le_trans (le_of_eq (by norm_num)) (BHH.shardN5r2_nonneg 1228800 1245184)

end BHH.Shards
