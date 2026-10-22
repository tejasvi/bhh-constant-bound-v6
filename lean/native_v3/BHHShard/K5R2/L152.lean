import BHH.ShardChainR2

namespace BHH.Shards

theorem k5r2_l152 : (0 : Int) ≤ BHH.Cert.shardN5r2 2490368 2506752 :=
  le_trans (le_of_eq (by norm_num)) (BHH.shardN5r2_nonneg 2490368 2506752)

end BHH.Shards
