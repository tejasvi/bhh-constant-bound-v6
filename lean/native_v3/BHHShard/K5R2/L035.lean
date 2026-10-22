import BHH.ShardChainR2
import BHHShard.K5R2.S035001
import BHHShard.K5R2.S035002
import BHHShard.K5R2.S035003
import BHHShard.K5R2.S035004

namespace BHH.Shards

theorem k5r2_l035 : (21318940233334877902065730068352440234343781755530771188422924768645120 : Int) ≤ BHH.Cert.shardN5r2 573440 589824 :=
  le_trans (le_of_eq (by norm_num)) (BHH.shardN5r2_add_le (by decide) (by decide) (BHH.shardN5r2_add_le (by decide) (by decide) (BHH.shardN5r2_add_le (by decide) (by decide) (BHH.shardN5r2_add_le (by decide) (by decide) (BHH.shardN5r2_nonneg 573440 584712) (BHH.le_shardN5r2_of_par BHH.Shards.k5r2_s035001)) (BHH.le_shardN5r2_of_par BHH.Shards.k5r2_s035002)) (BHH.le_shardN5r2_of_par BHH.Shards.k5r2_s035003)) (BHH.le_shardN5r2_of_par BHH.Shards.k5r2_s035004))

end BHH.Shards
