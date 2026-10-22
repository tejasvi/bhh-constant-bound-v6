import BHH.ShardChain
import BHHShard.K4.G0001
import BHHShard.K4.G0002
import BHHShard.K4.G0003
import BHHShard.K4.G0004
import BHHShard.K4.G0005
import BHHShard.K4.G0006
import BHHShard.K4.G0007
import BHHShard.K4.G0008
import BHHShard.K4.G0009
import BHHShard.K4.G0010
import BHHShard.K4.G0011
import BHHShard.K4.G0012

namespace BHH.Shards

theorem k4_all : (847856477421925944617776578172270653763708588816714556749897676546662999221 : Int) ≤ BHH.Cert.shardN 4 0 (2 ^ BHH.Cert.RN 4) :=
  le_trans (le_of_eq (by norm_num)) (BHH.shardN_add_le (by decide) (by decide) (BHH.shardN_add_le (by decide) (by decide) (BHH.shardN_add_le (by decide) (by decide) (BHH.shardN_add_le (by decide) (by decide) (BHH.shardN_add_le (by decide) (by decide) (BHH.shardN_add_le (by decide) (by decide) (BHH.shardN_add_le (by decide) (by decide) (BHH.shardN_add_le (by decide) (by decide) (BHH.shardN_add_le (by decide) (by decide) (BHH.shardN_add_le (by decide) (by decide) (BHH.shardN_add_le (by decide) (by decide) BHH.Shards.k4_g0001 BHH.Shards.k4_g0002) BHH.Shards.k4_g0003) BHH.Shards.k4_g0004) BHH.Shards.k4_g0005) BHH.Shards.k4_g0006) BHH.Shards.k4_g0007) BHH.Shards.k4_g0008) BHH.Shards.k4_g0009) BHH.Shards.k4_g0010) BHH.Shards.k4_g0011) BHH.Shards.k4_g0012)

end BHH.Shards
