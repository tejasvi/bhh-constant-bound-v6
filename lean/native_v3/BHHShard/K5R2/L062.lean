import BHH.ShardChainR2
import BHHShard.K5R2.S06204001
import BHHShard.K5R2.S06204002
import BHHShard.K5R2.S06204003
import BHHShard.K5R2.S06204004
import BHHShard.K5R2.S06206001

namespace BHH.Shards

theorem k5r2_l062 : (194335241825867631065517752370754374848224210120065341962224597901489051 : Int) ≤ BHH.Cert.shardN5r2 1015808 1032192 :=
  le_trans (le_of_eq (by norm_num)) (BHH.shardN5r2_add_le (by decide) (by decide) (BHH.shardN5r2_add_le (by decide) (by decide) (BHH.shardN5r2_add_le (by decide) (by decide) (BHH.shardN5r2_add_le (by decide) (by decide) (BHH.shardN5r2_add_le (by decide) (by decide) (BHH.shardN5r2_add_le (by decide) (by decide) (BHH.shardN5r2_add_le (by decide) (by decide) (BHH.shardN5r2_add_le (by decide) (by decide) (BHH.shardN5r2_add_le (by decide) (by decide) (BHH.shardN5r2_add_le (by decide) (by decide) (BHH.shardN5r2_add_le (by decide) (by decide) (BHH.shardN5r2_add_le (by decide) (by decide) (BHH.shardN5r2_nonneg 1015808 1017856) (BHH.shardN5r2_nonneg 1017856 1019904)) (BHH.shardN5r2_nonneg 1019904 1021952)) (BHH.shardN5r2_nonneg 1021952 1024000)) (BHH.shardN5r2_nonneg 1024000 1024002)) (BHH.le_shardN5r2_of_par BHH.Shards.k5r2_s06204001)) (BHH.le_shardN5r2_of_par BHH.Shards.k5r2_s06204002)) (BHH.le_shardN5r2_of_par BHH.Shards.k5r2_s06204003)) (BHH.le_shardN5r2_of_par BHH.Shards.k5r2_s06204004)) (BHH.shardN5r2_nonneg 1026048 1028096)) (BHH.shardN5r2_nonneg 1028096 1028435)) (BHH.le_shardN5r2_of_par BHH.Shards.k5r2_s06206001)) (BHH.shardN5r2_nonneg 1030144 1032192))

end BHH.Shards
