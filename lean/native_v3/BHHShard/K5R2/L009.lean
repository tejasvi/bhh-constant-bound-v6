import BHH.ShardChainR2
import BHHShard.K5R2.S009001

namespace BHH.Shards

theorem k5r2_l009 : (3845451535743298438733514896767469461391354561634407723685713233 : Int) ≤ BHH.Cert.shardN5r2 147456 163840 :=
  le_trans (le_of_eq (by norm_num)) (BHH.shardN5r2_add_le (by decide) (by decide) (BHH.shardN5r2_nonneg 147456 162082) (BHH.le_shardN5r2_of_par BHH.Shards.k5r2_s009001))

end BHH.Shards
