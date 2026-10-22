/-
Faster exact-arithmetic candidates for the kernel-only proof (untrusted, as `exactCand` / `exactAsin` in BHHCert/CandK.lean): the
same formulas, written for the kernel. The integer square root starts from a bisection on shifts instead of
`Nat.log2` (not accelerated by the kernel), tests are Boolean, signs come from the `Int` constructors, and the atan
series has 14 terms instead of 22 (after two halvings `z ≤ tan(π/16)`, so the truncation error is below `2^-66`; the
arcs are certified at `2^-62` at best). Every candidate is certified by `certArc` / `asinHi` / `asinLo`, so these
functions need no proof; only the leaf values (the certified arc endpoints) change in the last bits.
-/
import BHHCert.CandK

namespace BHH.Cert

/-- bisection for the bit length of `n`: the invariants `n >>> lo ≠ 0` (or `lo = 0`) and `n >>> hi = 0` -/
def bitLenK (n : Nat) : Nat → Nat → Nat → Nat
  | 0, _, hi => hi
  | fuel + 1, lo, hi =>
    bif Nat.ble hi (lo + 1) then hi else
    let mid := (lo + hi) / 2
    bif Nat.beq (n >>> mid) 0 then bitLenK n fuel lo mid else bitLenK n fuel mid hi

/-- Newton steps for the floor square root, with a Boolean test -/
def isqrtGoK (n : Nat) : Nat → Nat → Nat
  | 0, x => x
  | fuel + 1, x => let y := (x + n / x) / 2; bif Nat.blt y x then isqrtGoK n fuel y else x

/-- floor square root (candidate), started at `2^⌈L/2⌉ ≥ √n` for the bit length `L` of `n < 2^4096` -/
def isqrtK (n : Nat) : Nat :=
  bif Nat.ble n 1 then n else isqrtGoK n 200 (2 ^ ((bitLenK n 13 0 4096 + 1) / 2))

/-- `x < 0`, from the constructor -/
@[inline] def isNegK (x : Int) : Bool :=
  match x with
  | .negSucc _ => true
  | .ofNat _ => false

/-- fixed-point product -/
@[inline] def fmulK (a b : Int) : Int := (a * b) >>> PR
/-- fixed-point quotient (`0` for `b = 0`) -/
@[inline] def fdivK (a b : Int) : Int := bif b == 0 then 0 else (a * ONE) / b
/-- fixed-point square root of `a` (`0` for `a ≤ 0`) -/
@[inline] def fsqrtK (a : Int) : Int := bif isNegK a || a == 0 then 0 else (isqrtK (a * ONE).toNat : Int)

/-- `atan z` for `0 ≤ z ≤ ~0.2` by 14 terms of the series -/
def atanSeriesK (z : Int) : Int :=
  let z2 := fmulK z z
  (List.range 14).foldl (fun (acc : Int × Int) n =>
    let (sum, pw) := acc            -- pw = z^(2n+1)
    let term := pw / (2 * n + 1 : Nat)
    (bif n % 2 == 0 then sum + term else sum - term, fmulK pw z2)) (0, z) |>.1

/-- `atan z` for `0 ≤ z ≤ 1`: two argument halvings `z ↦ z / (1 + √(1 + z²))`, then the series -/
def atanUnitK (z : Int) : Int :=
  let h (w : Int) : Int := fdivK w (ONE + fsqrtK (ONE + fmulK w w))
  4 * atanSeriesK (h (h z))

/-- `atan2(y, x)` in fixed point (approximate) -/
def atan2FixK (y x : Int) : Int :=
  bif x == 0 && y == 0 then 0 else
  let ax := x.natAbs
  let ay := y.natAbs
  let base : Int := bif Nat.ble ay ax then atanUnitK (fdivK ay ax) else (piLo / 2) - atanUnitK (fdivK ax ay)
  let q : Int := bif isNegK x then piLo - base else base
  bif isNegK y then -q else q

/-- candidates `ψ ∓ α`, `ψ = atan2(wy, wx)`, `α = acos(√d2 / (2R))` (as `exactCand`) -/
def fastCand : CandFn := fun wx wy d2 R =>
  let psi := atan2FixK wy wx
  let d := (isqrtK d2.toNat : Int)                          -- d2 at scale 2^-2PR, d at 2^-PR
  let u := fdivK d (2 * R)
  let u' := bif Nat.blt ONE.toNat u.toNat then ONE else u
  let al := atan2FixK (fsqrtK (ONE - fmulK u' u')) u'
  (psi - al, psi + al)

/-- candidate `arcsin x = atan2(x, √(1 - x²))` (as `exactAsin`) -/
def fastAsin : AsinFn := fun x =>
  let x' := bif Nat.blt ONE.toNat x.toNat then ONE else bif Nat.blt ONE.toNat (-x).toNat then -ONE else x
  atan2FixK x' (fsqrtK (ONE - fmulK x' x'))

end BHH.Cert
