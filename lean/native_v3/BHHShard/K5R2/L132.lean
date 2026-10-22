import BHH.ShardChainR2

namespace BHH.Shards

theorem k5r2_l132 : (0 : Int) ≤ BHH.Cert.shardN5r2 2162688 2179072 :=
  le_trans (le_of_eq (by norm_num)) (BHH.shardN5r2_nonneg 2162688 2179072)

end BHH.Shards
