/-
Candidate arc endpoints and arcsin values in exact integer arithmetic (track K: no Float).  Never trusted: every
candidate is certified by `certArc` / `asinHi` / `asinLo`.  Kernel-friendly (structural recursion only).
-/
import BHHCert.Leaf

namespace BHH.Cert

/-- fixed-point product -/
@[inline] def fmul (a b : Int) : Int := (a * b) >>> PR
/-- fixed-point quotient (b ≠ 0) -/
@[inline] def fdiv (a b : Int) : Int := if b == 0 then 0 else (a * ONE) / b
/-- fixed-point square root of a ≥ 0 -/
@[inline] def fsqrt (a : Int) : Int := if a ≤ 0 then 0 else (isqrtCand (a * ONE).toNat : Int)

/-- `atan z` for `0 ≤ z ≤ ~0.2` by 22 terms of the series -/
def atanSeries (z : Int) : Int :=
  let z2 := fmul z z
  (List.range 22).foldl (fun (acc : Int × Int) n =>
    let (sum, pw) := acc            -- pw = z^(2n+1)
    let term := pw / (2 * n + 1 : Nat)
    (if n % 2 == 0 then sum + term else sum - term, fmul pw z2)) (0, z) |>.1

/-- `atan z` for `0 ≤ z ≤ 1`: two argument halvings `z ↦ z / (1 + √(1 + z²))`, then the series -/
def atanUnit (z : Int) : Int :=
  let h (w : Int) : Int := fdiv w (ONE + fsqrt (ONE + fmul w w))
  4 * atanSeries (h (h z))

/-- `atan2(y, x)` in fixed point (approximate) -/
def atan2Fix (y x : Int) : Int :=
  if x == 0 ∧ y == 0 then 0 else
  let ax := x.natAbs
  let ay := y.natAbs
  let base : Int := if ay ≤ ax then atanUnit (fdiv ay ax) else (piLo / 2) - atanUnit (fdiv ax ay)
  let q : Int := if x < 0 then piLo - base else base
  if y < 0 then -q else q

/-- exact-arithmetic candidates `ψ ∓ α`, `ψ = atan2(wy, wx)`, `α = acos(√d2 / (2R))` -/
def exactCand : CandFn := fun wx wy d2 R =>
  let psi := atan2Fix wy wx
  let d := (isqrtCand d2.toNat : Int)                       -- d2 at scale 2^-2PR, d at 2^-PR
  let u := fdiv d (2 * R)
  let u' := if u > ONE then ONE else u
  let al := atan2Fix (fsqrt (ONE - fmul u' u')) u'
  (psi - al, psi + al)

/-- exact-arithmetic candidate `arcsin x = atan2(x, √(1 - x²))` -/
def exactAsin : AsinFn := fun x =>
  let x' := if x > ONE then ONE else if x < -ONE then -ONE else x
  atan2Fix x' (fsqrt (ONE - fmul x' x'))

end BHH.Cert
