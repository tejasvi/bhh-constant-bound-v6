import BHH.ShardChainR2

namespace BHH.Shards

theorem k5r2_l028 : (0 : Int) ≤ BHH.Cert.shardN5r2 458752 475136 :=
  le_trans (le_of_eq (by norm_num)) (BHH.shardN5r2_nonneg 458752 475136)

end BHH.Shards
