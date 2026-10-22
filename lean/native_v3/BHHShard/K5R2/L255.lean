import BHH.ShardChainR2

namespace BHH.Shards

theorem k5r2_l255 : (0 : Int) ≤ BHH.Cert.shardN5r2 4177920 4194304 :=
  le_trans (le_of_eq (by norm_num)) (BHH.shardN5r2_nonneg 4177920 4194304)

end BHH.Shards
