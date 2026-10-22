import BHH.ShardChainR2
import BHHShard.K5R2.S243001

namespace BHH.Shards

theorem k5r2_l243 : (21209106747336204166616033409763608149520236277744146652872520265689 : Int) ≤ BHH.Cert.shardN5r2 3981312 3997696 :=
  le_trans (le_of_eq (by norm_num)) (BHH.shardN5r2_add_le (by decide) (by decide) (BHH.shardN5r2_nonneg 3981312 3992588) (BHH.le_shardN5r2_of_par BHH.Shards.k5r2_s243001))

end BHH.Shards
