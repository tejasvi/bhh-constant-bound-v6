import W2Prod.Claims
open W2C

namespace W2C.prod

/-- The t-integral (`2^8` sub-intervals per grid step) of the claimed enclosures gives
`Σ_{k=6}^{30} C_k ≥ 26853042 / 10^10`. -/
theorem tint : tintOK dtl T kmax 8 claims 26853042 (10 ^ 10) = true := by native_decide

end W2C.prod
