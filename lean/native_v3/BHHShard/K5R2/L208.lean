import BHH.ShardChainR2
import BHHShard.K5R2.G208_00
import BHHShard.K5R2.G208_01
import BHHShard.K5R2.G208_02
import BHHShard.K5R2.G208_03

namespace BHH.Shards

theorem k5r2_l208 : (20207179409853655240728004590004035293032722475340547913548394210241130910 : Int) ≤ BHH.Cert.shardN5r2 3407872 3424256 :=
  le_trans (le_of_eq (by norm_num)) (BHH.shardN5r2_add_le (by decide) (by decide) (BHH.shardN5r2_add_le (by decide) (by decide) (BHH.shardN5r2_add_le (by decide) (by decide) BHH.Shards.k5r2_g208_00 BHH.Shards.k5r2_g208_01) BHH.Shards.k5r2_g208_02) BHH.Shards.k5r2_g208_03)

end BHH.Shards
