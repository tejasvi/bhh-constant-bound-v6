import BHH.ShardChainR2

namespace BHH.Shards

theorem k5r2_l036 : (0 : Int) ≤ BHH.Cert.shardN5r2 589824 606208 :=
  le_trans (le_of_eq (by norm_num)) (BHH.shardN5r2_nonneg 589824 606208)

end BHH.Shards
