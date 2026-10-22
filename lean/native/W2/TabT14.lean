/-
T1–T4 of `W2/TabProps.lean`: the interval soundness of the table data (`RingSound`, `AngleSound`, `AngleRange`,
`FrangeSound`, `DistSound`), from the proofs in `W2/TabRing.lean`, `W2/TabAngle.lean`, `W2/TabFrange.lean`,
`W2/TabDist.lean`.
-/
import W2.TabProps
import W2.TabRing
import W2.TabFrange
import W2.TabDist

namespace BHH.W2.TabB

open BHH BHH.W2 W2C

/-- T1 -/
theorem ringSound : RingSound := fun g h1 h2 hNT hS j _ hden hhalf => ringSound_of g h1 h2 hNT hS j hden hhalf

/-- T2 -/
theorem angleSound : AngleSound := fun g h2 h30 => angleSound_of g h2 h30

/-- T2 -/
theorem angleRange : AngleRange := fun h d N hh hN hd φ φ' h1 h2 h3 h4 => angleRange_of h d N hh hN hd φ φ' h1 h2 h3 h4

/-- T3 -/
theorem frangeSound : FrangeSound := frange_sound

/-- T4 -/
theorem distSound : DistSound :=
  ⟨distHi_sound, epsCell_sound, fun ax ay bx by_ lx ly _ _ hdc => vertexDistHi_sound ax ay bx by_ lx ly hdc⟩

end BHH.W2.TabB
