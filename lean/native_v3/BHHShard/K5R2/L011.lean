import BHH.ShardChainR2
import BHHShard.K5R2.S011001

namespace BHH.Shards

theorem k5r2_l011 : (14963092527241735539159190157146002455017104554454159384460985479055968 : Int) ≤ BHH.Cert.shardN5r2 180224 196608 :=
  le_trans (le_of_eq (by norm_num)) (BHH.shardN5r2_add_le (by decide) (by decide) (BHH.shardN5r2_nonneg 180224 194592) (BHH.le_shardN5r2_of_par BHH.Shards.k5r2_s011001))

end BHH.Shards
