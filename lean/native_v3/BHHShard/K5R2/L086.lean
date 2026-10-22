import BHH.ShardChainR2
import BHHShard.K5R2.G086_00
import BHHShard.K5R2.G086_01

namespace BHH.Shards

theorem k5r2_l086 : (932800369125088926285036539546136716189019931061368351175969788805733370 : Int) ≤ BHH.Cert.shardN5r2 1409024 1425408 :=
  le_trans (le_of_eq (by norm_num)) (BHH.shardN5r2_add_le (by decide) (by decide) BHH.Shards.k5r2_g086_00 BHH.Shards.k5r2_g086_01)

end BHH.Shards
