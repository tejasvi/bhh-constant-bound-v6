import BHH.ShardChainR2

namespace BHH.Shards

theorem k5r2_l173 : (0 : Int) ≤ BHH.Cert.shardN5r2 2834432 2850816 :=
  le_trans (le_of_eq (by norm_num)) (BHH.shardN5r2_nonneg 2834432 2850816)

end BHH.Shards
