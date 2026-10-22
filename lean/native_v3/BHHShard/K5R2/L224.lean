import BHH.ShardChainR2

namespace BHH.Shards

theorem k5r2_l224 : (0 : Int) ≤ BHH.Cert.shardN5r2 3670016 3686400 :=
  le_trans (le_of_eq (by norm_num)) (BHH.shardN5r2_nonneg 3670016 3686400)

end BHH.Shards
