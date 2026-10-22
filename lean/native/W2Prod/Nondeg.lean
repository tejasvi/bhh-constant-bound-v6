import W2.EntryDefs
import W2Prod.Claims
open W2C

namespace W2C.prod

/-- The production grid passes the nondegeneracy tests: every interval denominator on the paths taken by `mkRing`
and `entryF` has a positive lower end. -/
theorem nondeg : nondegOK grid = true := by native_decide

end W2C.prod
