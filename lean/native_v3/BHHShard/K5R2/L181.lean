import BHH.ShardChainR2

namespace BHH.Shards

theorem k5r2_l181 : (0 : Int) ≤ BHH.Cert.shardN5r2 2965504 2981888 :=
  le_trans (le_of_eq (by norm_num)) (BHH.shardN5r2_nonneg 2965504 2981888)

end BHH.Shards
