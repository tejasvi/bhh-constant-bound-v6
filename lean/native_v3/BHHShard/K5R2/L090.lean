import BHH.ShardChainR2
import BHHShard.K5R2.G090_00
import BHHShard.K5R2.G090_01
import BHHShard.K5R2.G090_02

namespace BHH.Shards

theorem k5r2_l090 : (9758836896473932491192323046890253057478569800599818861028837384591708902 : Int) ≤ BHH.Cert.shardN5r2 1474560 1490944 :=
  le_trans (le_of_eq (by norm_num)) (BHH.shardN5r2_add_le (by decide) (by decide) (BHH.shardN5r2_add_le (by decide) (by decide) BHH.Shards.k5r2_g090_00 BHH.Shards.k5r2_g090_01) BHH.Shards.k5r2_g090_02)

end BHH.Shards
