import BHH.ShardChainR2
import BHHShard.K5R2.S022001
import BHHShard.K5R2.S022002

namespace BHH.Shards

theorem k5r2_l022 : (138229043472436030984427081560712852799632532413514291318642705910281171 : Int) ≤ BHH.Cert.shardN5r2 360448 376832 :=
  le_trans (le_of_eq (by norm_num)) (BHH.shardN5r2_add_le (by decide) (by decide) (BHH.shardN5r2_add_le (by decide) (by decide) (BHH.shardN5r2_nonneg 360448 373802) (BHH.le_shardN5r2_of_par BHH.Shards.k5r2_s022001)) (BHH.le_shardN5r2_of_par BHH.Shards.k5r2_s022002))

end BHH.Shards
