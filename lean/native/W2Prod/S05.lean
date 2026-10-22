import W2Cert.Shard
import W2Prod.Claims
open W2C

namespace W2C.prod

/-- Shard 5 of 8: the grid points `t_j` with `j % 8 = 5`. -/
theorem shard05 :
    shardOK grid dtl kmax true (claims.filter fun c => c.1 % 8 == 5) = true := by
  native_decide

end W2C.prod
