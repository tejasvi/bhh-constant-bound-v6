import BHH.ShardChainR2
import BHHShard.K5R2.S218001
import BHHShard.K5R2.S218002

namespace BHH.Shards

theorem k5r2_l218 : (88718525353599796785609674816275119058050218310768870727846198753026761 : Int) ≤ BHH.Cert.shardN5r2 3571712 3588096 :=
  le_trans (le_of_eq (by norm_num)) (BHH.shardN5r2_add_le (by decide) (by decide) (BHH.shardN5r2_add_le (by decide) (by decide) (BHH.shardN5r2_nonneg 3571712 3586052) (BHH.le_shardN5r2_of_par BHH.Shards.k5r2_s218001)) (BHH.le_shardN5r2_of_par BHH.Shards.k5r2_s218002))

end BHH.Shards
