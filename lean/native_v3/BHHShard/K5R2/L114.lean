import BHH.ShardChainR2
import BHHShard.K5R2.G114_00
import BHHShard.K5R2.G114_01
import BHHShard.K5R2.G114_02

namespace BHH.Shards

theorem k5r2_l114 : (12412202783473897443421131396765623543977558111204386986715220377042228611 : Int) ≤ BHH.Cert.shardN5r2 1867776 1884160 :=
  le_trans (le_of_eq (by norm_num)) (BHH.shardN5r2_add_le (by decide) (by decide) (BHH.shardN5r2_add_le (by decide) (by decide) BHH.Shards.k5r2_g114_00 BHH.Shards.k5r2_g114_01) BHH.Shards.k5r2_g114_02)

end BHH.Shards
