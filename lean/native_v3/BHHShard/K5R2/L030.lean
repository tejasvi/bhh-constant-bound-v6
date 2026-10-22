import BHH.ShardChainR2
import BHHShard.K5R2.S03006001
import BHHShard.K5R2.S03006002
import BHHShard.K5R2.S03006003

namespace BHH.Shards

theorem k5r2_l030 : (142136721113363410572745807370484989606902148194724554724363754908314385 : Int) ≤ BHH.Cert.shardN5r2 491520 507904 :=
  le_trans (le_of_eq (by norm_num)) (BHH.shardN5r2_add_le (by decide) (by decide) (BHH.shardN5r2_add_le (by decide) (by decide) (BHH.shardN5r2_add_le (by decide) (by decide) (BHH.shardN5r2_add_le (by decide) (by decide) (BHH.shardN5r2_add_le (by decide) (by decide) (BHH.shardN5r2_add_le (by decide) (by decide) (BHH.shardN5r2_add_le (by decide) (by decide) (BHH.shardN5r2_add_le (by decide) (by decide) (BHH.shardN5r2_add_le (by decide) (by decide) (BHH.shardN5r2_add_le (by decide) (by decide) (BHH.shardN5r2_nonneg 491520 493568) (BHH.shardN5r2_nonneg 493568 495616)) (BHH.shardN5r2_nonneg 495616 497664)) (BHH.shardN5r2_nonneg 497664 499712)) (BHH.shardN5r2_nonneg 499712 501760)) (BHH.shardN5r2_nonneg 501760 503808)) (BHH.shardN5r2_nonneg 503808 503842)) (BHH.le_shardN5r2_of_par BHH.Shards.k5r2_s03006001)) (BHH.le_shardN5r2_of_par BHH.Shards.k5r2_s03006002)) (BHH.le_shardN5r2_of_par BHH.Shards.k5r2_s03006003)) (BHH.shardN5r2_nonneg 505856 507904))

end BHH.Shards
