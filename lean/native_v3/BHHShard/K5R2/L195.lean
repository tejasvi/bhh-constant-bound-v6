import BHH.ShardChainR2

namespace BHH.Shards

theorem k5r2_l195 : (0 : Int) ≤ BHH.Cert.shardN5r2 3194880 3211264 :=
  le_trans (le_of_eq (by norm_num)) (BHH.shardN5r2_nonneg 3194880 3211264)

end BHH.Shards
