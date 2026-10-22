import BHH.ShardChainR2
import BHHShard.K5R2.S091001

namespace BHH.Shards

theorem k5r2_l091 : (10336617550383191372886600975712543805334218331901356638152777990664724 : Int) ≤ BHH.Cert.shardN5r2 1490944 1507328 :=
  le_trans (le_of_eq (by norm_num)) (BHH.shardN5r2_add_le (by decide) (by decide) (BHH.shardN5r2_nonneg 1490944 1495050) (BHH.le_shardN5r2_of_par BHH.Shards.k5r2_s091001))

end BHH.Shards
