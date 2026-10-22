import BHH.ShardChainR2

namespace BHH.Shards

theorem k5r2_l239 : (0 : Int) ≤ BHH.Cert.shardN5r2 3915776 3932160 :=
  le_trans (le_of_eq (by norm_num)) (BHH.shardN5r2_nonneg 3915776 3932160)

end BHH.Shards
