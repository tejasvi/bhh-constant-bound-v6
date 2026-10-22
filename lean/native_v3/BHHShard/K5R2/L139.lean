import BHH.ShardChainR2

namespace BHH.Shards

theorem k5r2_l139 : (0 : Int) ≤ BHH.Cert.shardN5r2 2277376 2293760 :=
  le_trans (le_of_eq (by norm_num)) (BHH.shardN5r2_nonneg 2277376 2293760)

end BHH.Shards
