import BHH.ShardChainR2

namespace BHH.Shards

theorem k5r2_l044 : (0 : Int) ≤ BHH.Cert.shardN5r2 720896 737280 :=
  le_trans (le_of_eq (by norm_num)) (BHH.shardN5r2_nonneg 720896 737280)

end BHH.Shards
