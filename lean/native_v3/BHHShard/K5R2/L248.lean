import BHH.ShardChainR2
import BHHShard.K5R2.G248_00
import BHHShard.K5R2.G248_01
import BHHShard.K5R2.G248_02
import BHHShard.K5R2.G248_03
import BHHShard.K5R2.G248_04
import BHHShard.K5R2.G248_05
import BHHShard.K5R2.G248_06
import BHHShard.K5R2.G248_07

namespace BHH.Shards

theorem k5r2_l248 : (38171854362186752235090439809278199079829596149407121098714212863306436730 : Int) ≤ BHH.Cert.shardN5r2 4063232 4079616 :=
  le_trans (le_of_eq (by norm_num)) (BHH.shardN5r2_add_le (by decide) (by decide) (BHH.shardN5r2_add_le (by decide) (by decide) (BHH.shardN5r2_add_le (by decide) (by decide) (BHH.shardN5r2_add_le (by decide) (by decide) (BHH.shardN5r2_add_le (by decide) (by decide) (BHH.shardN5r2_add_le (by decide) (by decide) (BHH.shardN5r2_add_le (by decide) (by decide) BHH.Shards.k5r2_g248_00 BHH.Shards.k5r2_g248_01) BHH.Shards.k5r2_g248_02) BHH.Shards.k5r2_g248_03) BHH.Shards.k5r2_g248_04) BHH.Shards.k5r2_g248_05) BHH.Shards.k5r2_g248_06) BHH.Shards.k5r2_g248_07)

end BHH.Shards
