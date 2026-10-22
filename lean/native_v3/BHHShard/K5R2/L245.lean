import BHH.ShardChainR2
import BHHShard.K5R2.S245001

namespace BHH.Shards

theorem k5r2_l245 : (1984877820035763750016831246021826432068475290137380817581724649640606 : Int) ≤ BHH.Cert.shardN5r2 4014080 4030464 :=
  le_trans (le_of_eq (by norm_num)) (BHH.shardN5r2_add_le (by decide) (by decide) (BHH.shardN5r2_nonneg 4014080 4015112) (BHH.le_shardN5r2_of_par BHH.Shards.k5r2_s245001))

end BHH.Shards
