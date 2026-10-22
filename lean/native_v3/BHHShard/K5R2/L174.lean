import BHH.ShardChainR2

namespace BHH.Shards

theorem k5r2_l174 : (0 : Int) ≤ BHH.Cert.shardN5r2 2850816 2867200 :=
  le_trans (le_of_eq (by norm_num)) (BHH.shardN5r2_nonneg 2850816 2867200)

end BHH.Shards
