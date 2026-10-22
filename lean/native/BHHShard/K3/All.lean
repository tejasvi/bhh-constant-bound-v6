import BHH.ShardChain
import BHHShard.K3.G0001

namespace BHH.Shards

theorem k3_all : (1948556198986259447252268280885767308299153975357199992777499749441278683487 : Int) ≤ BHH.Cert.shardN 3 0 (2 ^ BHH.Cert.RN 3) :=
  le_trans (le_of_eq (by norm_num)) BHH.Shards.k3_g0001

end BHH.Shards
