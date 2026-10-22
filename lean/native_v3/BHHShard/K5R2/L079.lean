import BHH.ShardChainR2

namespace BHH.Shards

theorem k5r2_l079 : (0 : Int) ≤ BHH.Cert.shardN5r2 1294336 1310720 :=
  le_trans (le_of_eq (by norm_num)) (BHH.shardN5r2_nonneg 1294336 1310720)

end BHH.Shards
