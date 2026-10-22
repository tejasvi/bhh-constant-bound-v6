import BHH.ShardChainR2
import BHHShard.K5R2.Q0
import BHHShard.K5R2.Q1
import BHHShard.K5R2.Q2
import BHHShard.K5R2.Q3

namespace BHH.Shards

theorem k5r2_all : (223587646079220345491004373434653562490729818146207255943503471376435910407 : Int) ≤ BHH.Cert.shardN5r2 0 (2 ^ BHH.Cert.RN 5) :=
  le_trans (le_of_eq (by norm_num)) (BHH.shardN5r2_add_le (by decide) (by decide) (BHH.shardN5r2_add_le (by decide) (by decide) (BHH.shardN5r2_add_le (by decide) (by decide) BHH.Shards.k5r2_q0 BHH.Shards.k5r2_q1) BHH.Shards.k5r2_q2) BHH.Shards.k5r2_q3)

end BHH.Shards
