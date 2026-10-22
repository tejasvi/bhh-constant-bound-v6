import BHH.ShardChainR2
import BHHShard.K5R2.S119001

namespace BHH.Shards

theorem k5r2_l119 : (27757742953914746860118267518825130308182065703114920385420856341865 : Int) ≤ BHH.Cert.shardN5r2 1949696 1966080 :=
  le_trans (le_of_eq (by norm_num)) (BHH.shardN5r2_add_le (by decide) (by decide) (BHH.shardN5r2_nonneg 1949696 1951002) (BHH.le_shardN5r2_of_par BHH.Shards.k5r2_s119001))

end BHH.Shards
