import BHH.ShardChainR2

namespace BHH.Shards

theorem k5r2_l078 : (0 : Int) ≤ BHH.Cert.shardN5r2 1277952 1294336 :=
  le_trans (le_of_eq (by norm_num)) (BHH.shardN5r2_nonneg 1277952 1294336)

end BHH.Shards
