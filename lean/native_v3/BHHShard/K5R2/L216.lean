import BHH.ShardChainR2
import BHHShard.K5R2.G216_00
import BHHShard.K5R2.G216_01
import BHHShard.K5R2.G216_02
import BHHShard.K5R2.G216_03

namespace BHH.Shards

theorem k5r2_l216 : (15877830134729573941742997231043893208361388893696011225322588072883493985 : Int) ≤ BHH.Cert.shardN5r2 3538944 3555328 :=
  le_trans (le_of_eq (by norm_num)) (BHH.shardN5r2_add_le (by decide) (by decide) (BHH.shardN5r2_add_le (by decide) (by decide) (BHH.shardN5r2_add_le (by decide) (by decide) BHH.Shards.k5r2_g216_00 BHH.Shards.k5r2_g216_01) BHH.Shards.k5r2_g216_02) BHH.Shards.k5r2_g216_03)

end BHH.Shards
