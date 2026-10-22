/-
Extra fixed-point interval functions for the window-2 tables (core Lean only), on top of
`BHHCert/Exact.lean` (`Iv` = `[lo, hi] / 2^PR`, `PR = 96`, outward rounding).

`arccos`, `arcsin` and `log` are obtained by verification: a candidate from `Float` (never trusted) is moved by a
small amount and checked with the verified `cos`/`sin`/`exp`; if every check fails, a trivially valid interval is
returned.  `exp` is a Taylor polynomial with Mathlib's `Real.exp_bound` remainder after argument halving.
-/
import BHHCert.Exact

namespace W2C
open BHH.Cert

/-- `2^-PR` as a Float -/
def fScale : Float := Float.scaleB 1.0 (-(PR : Int))

/-- Float value of a fixed-point integer (approximate, untrusted). -/
def toF (n : Int) : Float := Float.ofInt n * fScale

/-- Fixed-point integer near the Float `x` (`|x| < 2^10`): `round(x 2^52) 2^(PR - 52)` (untrusted). -/
def ofF (x : Float) : Int := (x * 4503599627370496.0).round.toInt64.toInt * 2 ^ (PR - 52)

/-- Offsets tried around (Newton-refined) candidates: `2^-84`, `2^-72`, `2^-60`, `2^-44`, `2^-30`, `2^-16`. -/
def offList : List Int :=
  [2 ^ (PR - 84), 2 ^ (PR - 72), 2 ^ (PR - 60), 2 ^ (PR - 44), 2 ^ (PR - 30), 2 ^ (PR - 16)]

/-- midpoint of an interval -/
def ivMid (a : Iv) : Int := (a.lo + a.hi) / 2

/-- first `some` among `f e`, `e ∈ offList` -/
def firstSome (f : Int → Option Int) : Option Int :=
  offList.foldl (fun acc e => match acc with | some v => some v | none => f e) none

/-- clamp to `[-1, 1]` (fixed point) -/
def clampOne (x : Int) : Int := Max.max (-ONE) (Min.min ONE x)

/-! ## arccos and arcsin -/

/-- One Newton step for `cos θ = a` from the Float candidate (untrusted). -/
def acosCand (a : Int) : Int :=
  let θ0 := ofF (Float.acos (toF (clampOne a)))
  let cs := cosSin θ0
  let s := ivMid cs.2
  if s == 0 then θ0 else θ0 + ((ivMid cs.1 - a) * ONE) / s

/-- One Newton step for `sin θ = a` from the Float candidate (untrusted). -/
def asinCand (a : Int) : Int :=
  let θ0 := ofF (Float.asin (toF (clampOne a)))
  let cs := cosSin θ0
  let c := ivMid cs.1
  if c == 0 then θ0 else θ0 - ((ivMid cs.2 - a) * ONE) / c


/-- Lower bound for `arccos x`, `x ≤ a / 2^PR`: a `θ ≤ π` with `cos θ ≥ a` (or `0`). -/
def acosLo (a : Int) : Int :=
  let θ0 := acosCand a
  (firstSome fun e =>
    let θ := θ0 - e
    if θ ≤ 0 then some 0
    else if θ ≤ piLo ∧ a ≤ (cosSin θ).1.lo then some θ else none).getD 0

/-- Upper bound for `arccos x`, `x ≥ a / 2^PR`: a `θ ≥ 0` with `cos θ ≤ a` (or `piHi`). -/
def acosHi (a : Int) : Int :=
  let θ0 := acosCand a
  (firstSome fun e =>
    let θ := θ0 + e
    if piHi ≤ θ then some piHi
    else if 0 ≤ θ ∧ (cosSin θ).1.hi ≤ a then some θ else none).getD piHi

/-- `arccos` of an interval (decreasing): `[acosLo a.hi, acosHi a.lo]`. -/
def acosIv (a : Iv) : Iv := ⟨acosLo a.hi, acosHi a.lo⟩

/-- `π/2` enclosure endpoints -/
def halfPiLo : Int := piLo / 2
def halfPiHi : Int := (piHi + 1) / 2

/-- Lower bound for `arcsin x`, `x ≥ a / 2^PR`: a `θ ≥ -π/2` with `sin θ ≤ a` (or `-halfPiHi`). -/
def asinLo (a : Int) : Int :=
  let θ0 := asinCand a
  (firstSome fun e =>
    let θ := θ0 - e
    if θ ≤ -halfPiHi then some (-halfPiHi)
    else if -halfPiLo ≤ θ ∧ θ ≤ halfPiLo ∧ (cosSin θ).2.hi ≤ a then some θ else none).getD (-halfPiHi)

/-- Upper bound for `arcsin x`, `x ≤ a / 2^PR`: a `θ ≤ π/2` with `sin θ ≥ a` (or `halfPiHi`). -/
def asinHi (a : Int) : Int :=
  let θ0 := asinCand a
  (firstSome fun e =>
    let θ := θ0 + e
    if halfPiHi ≤ θ then some halfPiHi
    else if -halfPiLo ≤ θ ∧ θ ≤ halfPiLo ∧ a ≤ (cosSin θ).2.lo then some θ else none).getD halfPiHi

/-- `arcsin` of an interval (increasing). -/
def asinIv (a : Iv) : Iv := ⟨asinLo a.lo, asinHi a.hi⟩

/-! ## exp -/

/-- Taylor sum `Σ_{m<n} y^m/m!` for `y = t / 2^(PR + r)` with interval terms; returns `(sum, last term)`. -/
def expTaylorGo (t : Int) (r n : Nat) : Nat → Nat → Iv → Iv → Iv × Iv
  | 0, _, term, s => (s, term)
  | fuel + 1, m, term, s =>
    if m == n then (s, term) else
    let s' := Iv.add s term
    let numLo := if 0 ≤ t then term.lo * t else term.hi * t
    let numHi := if 0 ≤ t then term.hi * t else term.lo * t
    let nt : Iv := ⟨divD (shrD numLo (PR + r)) (m + 1), divU (shrU numHi (PR + r)) (m + 1)⟩
    expTaylorGo t r n fuel (m + 1) nt s'

/-- Number of Taylor terms for `exp` on `|y| ≤ 1/2`. -/
def EXPN : Nat := 30

/-- `exp y` for `y = t / 2^(PR + r)`, `|y| ≤ 1`: Taylor sum plus `|y|^n (n+1)/(n! n)` (Mathlib `Real.exp_bound`;
the last term returned is `y^n/n!`). -/
def expSmall (t : Int) (r : Nat) : Iv :=
  let (s, last) := expTaylorGo t r EXPN (EXPN + 1) 0 (Iv.int 1) ⟨0, 0⟩
  let mag := Max.max (Int.natAbs last.lo) (Int.natAbs last.hi)
  let rem : Int := divU (mag * (EXPN + 1)) EXPN + 1
  Iv.widen s rem

/-- square of a positive interval, `n` times -/
def sqrN : Nat → Iv → Iv
  | 0, a => a
  | n + 1, a => sqrN n (Iv.sqr a)

/-- Halvings so that `|t| / 2^(PR + r) ≤ 1/2`. -/
def expShift (t : Int) : Nat :=
  let m := t.natAbs
  if m ≤ ONE.toNat / 2 then 0 else Nat.log2 (m / (ONE.toNat / 2)) + 1

/-- `exp x` for the exact point `x = t / 2^PR`, `|x| ≤ 1024` (else a trivial `[0, 2^200]`). -/
def expPt (t : Int) : Iv :=
  if t.natAbs ≤ 1024 * ONE.toNat then
    let r := expShift t
    let e := sqrN r (expSmall t r)
    ⟨Max.max e.lo 0, e.hi⟩
  else ⟨0, 2 ^ 200⟩

/-- `exp` of an interval (increasing). -/
def expIv (a : Iv) : Iv := ⟨(expPt a.lo).lo, (expPt a.hi).hi⟩

/-! ## log -/

/-- One Newton step for `exp θ = a` from the Float candidate (untrusted). -/
def logCand (a : Int) : Int :=
  let θ0 := ofF (Float.log (toF a))
  let e := ivMid (expPt θ0)
  if e ≤ 0 then θ0 else θ0 + (a * ONE) / e - ONE

/-- Lower bound for `log x`, `x ≥ a / 2^PR > 0`: a `θ` with `exp θ ≤ a`. -/
def logLo (a : Int) : Int :=
  if a ≤ 0 then -(2 ^ 200) else
  let θ0 := logCand a
  (firstSome fun e =>
    let θ := θ0 - e
    if θ.natAbs ≤ 1024 * ONE.toNat ∧ (expPt θ).hi ≤ a then some θ else none).getD (-(2 ^ 200))

/-- Upper bound for `log x`, `x ≤ a / 2^PR`: a `θ` with `exp θ ≥ a`. -/
def logHi (a : Int) : Int :=
  if a ≤ 0 then -(2 ^ 200) else
  let θ0 := logCand a
  (firstSome fun e =>
    let θ := θ0 + e
    if a ≤ (expPt θ).lo then some θ else none).getD (2 ^ 200)

/-- `log` of a positive interval (increasing). -/
def logIv (a : Iv) : Iv := ⟨logLo a.lo, logHi a.hi⟩

/-! ## the area `A_1(r) = |B(z,1) \ B(0,1)|`, `|z| = r` -/

/-- `A_1(p) = π - 2 arccos(p/2) + (p/2) √(4 - p²)` for the exact point `p / 2^PR`, `0 ≤ p`; `π` for `p ≥ 2`. -/
def a1Pt (p : Int) : Iv :=
  if 2 * ONE ≤ p then piIv
  else
    let h := Iv.div2e (Iv.pt p) 1                       -- p/2 (rounded outward)
    let ac := acosIv h
    let s := Iv.sqrt (Iv.sub (Iv.int 4) (Iv.sqr (Iv.pt p)))
    Iv.add (Iv.sub piIv (Iv.mul2e ac 1)) (Iv.mul h s)

/-- `A_1` of an interval `r ⊆ [0, ∞)` (increasing): `[A_1(r.lo).lo, A_1(r.hi).hi]`. -/
def a1Iv (r : Iv) : Iv := ⟨(a1Pt (Max.max r.lo 0)).lo, (a1Pt (Max.max r.hi 0)).hi⟩

end W2C
