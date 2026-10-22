import BHH.ShardChainR2

namespace BHH.Shards

theorem k5r2_l176 : (0 : Int) ≤ BHH.Cert.shardN5r2 2883584 2899968 :=
  le_trans (le_of_eq (by norm_num)) (BHH.shardN5r2_nonneg 2883584 2899968)

end BHH.Shards
