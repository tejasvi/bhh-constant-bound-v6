import BHH.ShardChainR2

namespace BHH.Shards

theorem k5r2_l183 : (0 : Int) ≤ BHH.Cert.shardN5r2 2998272 3014656 :=
  le_trans (le_of_eq (by norm_num)) (BHH.shardN5r2_nonneg 2998272 3014656)

end BHH.Shards
