import BHH.ShardChainR2

namespace BHH.Shards

theorem k5r2_l231 : (0 : Int) ≤ BHH.Cert.shardN5r2 3784704 3801088 :=
  le_trans (le_of_eq (by norm_num)) (BHH.shardN5r2_nonneg 3784704 3801088)

end BHH.Shards
