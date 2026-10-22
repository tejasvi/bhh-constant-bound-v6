import BHH.ShardChainR2

namespace BHH.Shards

theorem k5r2_l201 : (0 : Int) ≤ BHH.Cert.shardN5r2 3293184 3309568 :=
  le_trans (le_of_eq (by norm_num)) (BHH.shardN5r2_nonneg 3293184 3309568)

end BHH.Shards
