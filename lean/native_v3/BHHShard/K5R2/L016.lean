import BHH.ShardChainR2
import BHHShard.K5R2.S016001

namespace BHH.Shards

theorem k5r2_l016 : (38479617224150843888124578791675454565521630958592323044819759258973071 : Int) ≤ BHH.Cert.shardN5r2 262144 278528 :=
  le_trans (le_of_eq (by norm_num)) (BHH.shardN5r2_add_le (by decide) (by decide) (BHH.shardN5r2_nonneg 262144 275714) (BHH.le_shardN5r2_of_par BHH.Shards.k5r2_s016001))

end BHH.Shards
