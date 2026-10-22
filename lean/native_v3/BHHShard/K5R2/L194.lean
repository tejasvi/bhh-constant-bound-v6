import BHH.ShardChainR2

namespace BHH.Shards

theorem k5r2_l194 : (0 : Int) ≤ BHH.Cert.shardN5r2 3178496 3194880 :=
  le_trans (le_of_eq (by norm_num)) (BHH.shardN5r2_nonneg 3178496 3194880)

end BHH.Shards
