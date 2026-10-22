import BHH.ShardChainR2

namespace BHH.Shards

theorem k5r2_g086_01 : (0 : Int) ≤ BHH.Cert.shardN5r2 1425152 1425408 :=
  le_trans (le_of_eq (by norm_num)) (BHH.shardN5r2_nonneg 1425152 1425408)

end BHH.Shards
