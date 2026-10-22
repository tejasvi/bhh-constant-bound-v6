import BHH.ShardChainR2

namespace BHH.Shards

theorem k5r2_l229 : (0 : Int) ≤ BHH.Cert.shardN5r2 3751936 3768320 :=
  le_trans (le_of_eq (by norm_num)) (BHH.shardN5r2_nonneg 3751936 3768320)

end BHH.Shards
