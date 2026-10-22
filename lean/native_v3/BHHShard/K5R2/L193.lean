import BHH.ShardChainR2

namespace BHH.Shards

theorem k5r2_l193 : (0 : Int) ≤ BHH.Cert.shardN5r2 3162112 3178496 :=
  le_trans (le_of_eq (by norm_num)) (BHH.shardN5r2_nonneg 3162112 3178496)

end BHH.Shards
