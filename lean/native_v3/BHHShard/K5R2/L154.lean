import BHH.ShardChainR2

namespace BHH.Shards

theorem k5r2_l154 : (0 : Int) ≤ BHH.Cert.shardN5r2 2523136 2539520 :=
  le_trans (le_of_eq (by norm_num)) (BHH.shardN5r2_nonneg 2523136 2539520)

end BHH.Shards
