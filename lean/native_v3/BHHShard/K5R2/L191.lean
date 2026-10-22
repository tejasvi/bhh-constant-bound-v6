import BHH.ShardChainR2

namespace BHH.Shards

theorem k5r2_l191 : (0 : Int) ≤ BHH.Cert.shardN5r2 3129344 3145728 :=
  le_trans (le_of_eq (by norm_num)) (BHH.shardN5r2_nonneg 3129344 3145728)

end BHH.Shards
