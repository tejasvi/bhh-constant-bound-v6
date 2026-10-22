import BHH.ShardChainR2

namespace BHH.Shards

theorem k5r2_l153 : (0 : Int) ≤ BHH.Cert.shardN5r2 2506752 2523136 :=
  le_trans (le_of_eq (by norm_num)) (BHH.shardN5r2_nonneg 2506752 2523136)

end BHH.Shards
