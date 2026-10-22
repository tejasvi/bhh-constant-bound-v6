import BHH.ShardChainR2

namespace BHH.Shards

theorem k5r2_l080 : (0 : Int) ≤ BHH.Cert.shardN5r2 1310720 1327104 :=
  le_trans (le_of_eq (by norm_num)) (BHH.shardN5r2_nonneg 1310720 1327104)

end BHH.Shards
