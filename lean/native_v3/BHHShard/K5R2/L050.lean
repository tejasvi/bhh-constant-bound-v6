import BHH.ShardChainR2
import BHHShard.K5R2.G050_00
import BHHShard.K5R2.G050_01

namespace BHH.Shards

theorem k5r2_l050 : (9348183979983614506001741631467996082998051666713469564426797580033766042 : Int) ≤ BHH.Cert.shardN5r2 819200 835584 :=
  le_trans (le_of_eq (by norm_num)) (BHH.shardN5r2_add_le (by decide) (by decide) BHH.Shards.k5r2_g050_00 BHH.Shards.k5r2_g050_01)

end BHH.Shards
