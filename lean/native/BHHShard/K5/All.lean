import BHH.ShardChain
import BHHShard.K5.G0001
import BHHShard.K5.G0002
import BHHShard.K5.G0003
import BHHShard.K5.G0004
import BHHShard.K5.G0005
import BHHShard.K5.G0006
import BHHShard.K5.G0007
import BHHShard.K5.G0008
import BHHShard.K5.G0009
import BHHShard.K5.G0010
import BHHShard.K5.G0011
import BHHShard.K5.G0012
import BHHShard.K5.G0013
import BHHShard.K5.G0014
import BHHShard.K5.G0015
import BHHShard.K5.G0016
import BHHShard.K5.G0017
import BHHShard.K5.G0018
import BHHShard.K5.G0019
import BHHShard.K5.G0020
import BHHShard.K5.G0021
import BHHShard.K5.G0022
import BHHShard.K5.G0023
import BHHShard.K5.G0024
import BHHShard.K5.G0025
import BHHShard.K5.G0026
import BHHShard.K5.G0027
import BHHShard.K5.G0028
import BHHShard.K5.G0029
import BHHShard.K5.G0030
import BHHShard.K5.G0031
import BHHShard.K5.G0032
import BHHShard.K5.G0033
import BHHShard.K5.G0034
import BHHShard.K5.G0035
import BHHShard.K5.G0036
import BHHShard.K5.G0037
import BHHShard.K5.G0038
import BHHShard.K5.G0039
import BHHShard.K5.G0040
import BHHShard.K5.G0041
import BHHShard.K5.G0042
import BHHShard.K5.G0043
import BHHShard.K5.G0044

namespace BHH.Shards

theorem k5_all : (215693327339043455696217336398543280179618358644157842708511676732176834801 : Int) ≤ BHH.Cert.shardN 5 0 (2 ^ BHH.Cert.RN 5) :=
  le_trans (le_of_eq (by norm_num)) (BHH.shardN_add_le (by decide) (by decide) (BHH.shardN_add_le (by decide) (by decide) (BHH.shardN_add_le (by decide) (by decide) (BHH.shardN_add_le (by decide) (by decide) (BHH.shardN_add_le (by decide) (by decide) (BHH.shardN_add_le (by decide) (by decide) (BHH.shardN_add_le (by decide) (by decide) (BHH.shardN_add_le (by decide) (by decide) (BHH.shardN_add_le (by decide) (by decide) (BHH.shardN_add_le (by decide) (by decide) (BHH.shardN_add_le (by decide) (by decide) (BHH.shardN_add_le (by decide) (by decide) (BHH.shardN_add_le (by decide) (by decide) (BHH.shardN_add_le (by decide) (by decide) (BHH.shardN_add_le (by decide) (by decide) (BHH.shardN_add_le (by decide) (by decide) (BHH.shardN_add_le (by decide) (by decide) (BHH.shardN_add_le (by decide) (by decide) (BHH.shardN_add_le (by decide) (by decide) (BHH.shardN_add_le (by decide) (by decide) (BHH.shardN_add_le (by decide) (by decide) (BHH.shardN_add_le (by decide) (by decide) (BHH.shardN_add_le (by decide) (by decide) (BHH.shardN_add_le (by decide) (by decide) (BHH.shardN_add_le (by decide) (by decide) (BHH.shardN_add_le (by decide) (by decide) (BHH.shardN_add_le (by decide) (by decide) (BHH.shardN_add_le (by decide) (by decide) (BHH.shardN_add_le (by decide) (by decide) (BHH.shardN_add_le (by decide) (by decide) (BHH.shardN_add_le (by decide) (by decide) (BHH.shardN_add_le (by decide) (by decide) (BHH.shardN_add_le (by decide) (by decide) (BHH.shardN_add_le (by decide) (by decide) (BHH.shardN_add_le (by decide) (by decide) (BHH.shardN_add_le (by decide) (by decide) (BHH.shardN_add_le (by decide) (by decide) (BHH.shardN_add_le (by decide) (by decide) (BHH.shardN_add_le (by decide) (by decide) (BHH.shardN_add_le (by decide) (by decide) (BHH.shardN_add_le (by decide) (by decide) (BHH.shardN_add_le (by decide) (by decide) (BHH.shardN_add_le (by decide) (by decide) BHH.Shards.k5_g0001 BHH.Shards.k5_g0002) BHH.Shards.k5_g0003) BHH.Shards.k5_g0004) BHH.Shards.k5_g0005) BHH.Shards.k5_g0006) BHH.Shards.k5_g0007) BHH.Shards.k5_g0008) BHH.Shards.k5_g0009) BHH.Shards.k5_g0010) BHH.Shards.k5_g0011) BHH.Shards.k5_g0012) BHH.Shards.k5_g0013) BHH.Shards.k5_g0014) BHH.Shards.k5_g0015) BHH.Shards.k5_g0016) BHH.Shards.k5_g0017) BHH.Shards.k5_g0018) BHH.Shards.k5_g0019) BHH.Shards.k5_g0020) BHH.Shards.k5_g0021) BHH.Shards.k5_g0022) BHH.Shards.k5_g0023) BHH.Shards.k5_g0024) BHH.Shards.k5_g0025) BHH.Shards.k5_g0026) BHH.Shards.k5_g0027) BHH.Shards.k5_g0028) BHH.Shards.k5_g0029) BHH.Shards.k5_g0030) BHH.Shards.k5_g0031) BHH.Shards.k5_g0032) BHH.Shards.k5_g0033) BHH.Shards.k5_g0034) BHH.Shards.k5_g0035) BHH.Shards.k5_g0036) BHH.Shards.k5_g0037) BHH.Shards.k5_g0038) BHH.Shards.k5_g0039) BHH.Shards.k5_g0040) BHH.Shards.k5_g0041) BHH.Shards.k5_g0042) BHH.Shards.k5_g0043) BHH.Shards.k5_g0044)

end BHH.Shards
