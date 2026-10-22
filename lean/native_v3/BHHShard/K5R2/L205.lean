import BHH.ShardChainR2

namespace BHH.Shards

theorem k5r2_l205 : (0 : Int) ≤ BHH.Cert.shardN5r2 3358720 3375104 :=
  le_trans (le_of_eq (by norm_num)) (BHH.shardN5r2_nonneg 3358720 3375104)

end BHH.Shards
