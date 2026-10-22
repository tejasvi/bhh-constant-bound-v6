import BHH.ShardChainR2

namespace BHH.Shards

theorem k5r2_l192 : (0 : Int) ≤ BHH.Cert.shardN5r2 3145728 3162112 :=
  le_trans (le_of_eq (by norm_num)) (BHH.shardN5r2_nonneg 3145728 3162112)

end BHH.Shards
