import BHH.ShardChainR2
import BHHShard.K5R2.S219001

namespace BHH.Shards

theorem k5r2_l219 : (2335476472882840317151786651461262837336892435629446429646410985394 : Int) ≤ BHH.Cert.shardN5r2 3588096 3604480 :=
  le_trans (le_of_eq (by norm_num)) (BHH.shardN5r2_add_le (by decide) (by decide) (BHH.shardN5r2_nonneg 3588096 3602944) (BHH.le_shardN5r2_of_par BHH.Shards.k5r2_s219001))

end BHH.Shards
