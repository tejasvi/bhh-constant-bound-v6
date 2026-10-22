import BHH.ShardChainR2

namespace BHH.Shards

theorem k5r2_l073 : (0 : Int) ≤ BHH.Cert.shardN5r2 1196032 1212416 :=
  le_trans (le_of_eq (by norm_num)) (BHH.shardN5r2_nonneg 1196032 1212416)

end BHH.Shards
