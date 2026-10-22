import BHH.ShardChainR2
import BHHShard.K5R2.S024001

namespace BHH.Shards

theorem k5r2_l024 : (37736549045892484136441985711406881947811612796239977691009650170269817 : Int) ≤ BHH.Cert.shardN5r2 393216 409600 :=
  le_trans (le_of_eq (by norm_num)) (BHH.shardN5r2_add_le (by decide) (by decide) (BHH.shardN5r2_nonneg 393216 405792) (BHH.le_shardN5r2_of_par BHH.Shards.k5r2_s024001))

end BHH.Shards
