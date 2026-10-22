import BHH.ShardChainR2

namespace BHH.Shards

theorem k5r2_l053 : (0 : Int) ≤ BHH.Cert.shardN5r2 868352 884736 :=
  le_trans (le_of_eq (by norm_num)) (BHH.shardN5r2_nonneg 868352 884736)

end BHH.Shards
