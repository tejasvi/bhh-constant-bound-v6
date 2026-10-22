/-
The t-integral of the window-2 bound (paper Section 4.4) in exact fixed-point arithmetic (core Lean only).

Input: for each `k` and each grid point `t_j = j 2^-dtl` (`1 ≤ j ≤ NTV`), an enclosure `lo ≤ Ψ_k^d(t_j) ≤ hi` with
`lo = ml 2^-sl`, `hi = mh 2^-sh`.  `ψ = log Ψ_k^d` is convex and nonincreasing.  On `[t_j, t_{j+1}]` three affine
minorants `α + β t` of `ψ` are used (the value at `t_{j+1}`, and the left and right extended secants with directed
slopes), and on `[0, t_1]` the value at `t_1`.  For each minorant, `∫ t^{s-1} e^{-π t} e^{α + β t} dt` over the
interval is bounded below by `Σ_m w √(f(a_m) f(b_m))` over `2^lsub` sub-intervals `[a_m, b_m]` of length `w`, where
`f(t) = t^{s-1} e^{α - γ t}`, `γ ≥ π - β` (`f` is log-concave for `s ≥ 1`, so `f(t) + f(a + b - t) ≥ 2√(f(a) f(b))`).
`C_k ≥ (1/2) Σ_j (the largest of the minorant integrals)`.
-/
import W2Cert.Fix

namespace W2C
open BHH.Cert

/-- `log 2` enclosure -/
def log2Iv : Iv := logIv (Iv.int 2)

/-- number of bits of `n` (`n > 0`) -/
def nbitsN (n : Nat) : Nat := Nat.log2 n + 1

/-- Lower (`lower = true`) or upper bound for `log(m 2^-sc)`, `m > 0`, fixed point. -/
def logScaled (lower : Bool) (m : Nat) (sc : Int) : Int :=
  let b := nbitsN m
  -- x = m 2^-b ∈ [1/2, 1) at scale 2^-PR, rounded in the direction of the bound
  let x : Int :=
    if b ≤ PR then (m * 2 ^ (PR - b) : Nat)
    else if lower then (m >>> (b - PR) : Nat) else ((m + 2 ^ (b - PR) - 1) >>> (b - PR) : Nat)
  let e : Int := (b : Int) - sc               -- log(m 2^-sc) = log x + e log 2
  let l2 := if (0 ≤ e) = lower then log2Iv.lo else log2Iv.hi
  if lower then logLo x + e * l2 else logHi x + e * l2

/-- Lower bound `X(t)` for `log f(t) = (s-1) log t + α - γ t` at `t = m 2^-q` (`m ≥ 1`), `s - 1 = (2k - 3)/2`,
`α` a lower bound, `γ` an upper bound, `logt` a lower bound for `log t` (all fixed point). -/
def xLo (k : Nat) (alpha gamma logt : Int) (m q : Nat) : Int :=
  let gt : Int := divU (gamma * m) (2 ^ q)
  alpha - gt + divD ((2 * (k : Int) - 3) * logt) 2

/-- Lower bound for `∫_a^b t^{s-1} e^{α - γ t} dt`, `a = ja 2^-dtl`, `b = a + 2^-dtl`, by `2^lsub` sub-intervals
`[a', b']` of length `w`: on each, with `X`, `Y` lower bounds of `log f(a')`, `log f(b')`, `M = (X + Y)/2`,
`D = Y - X` and `κ = (s-1)/(2 b'^2)`, `∫_{a'}^{b'} f ≥ w e^M (1 + D²/24 + κ w²/6)` (log-concavity with curvature
`≥ 2κ`, then pairing `t` with `a' + b' - t`: `cosh u ≥ 1 + u²/2`, `e^x ≥ 1 + x`, `∫ (t - a')(b' - t) = w³/6`).
`logs[i]` is a lower bound for `log(i 2^-(dtl + lsub))` (`i ≥ 1`). -/
def segLo (k : Nat) (alpha gamma : Int) (ja dtl lsub : Nat) (logs : Array Int) : Int :=
  let n := 2 ^ lsub
  let q := dtl + lsub
  let i0 := ja * n
  let xAt (i : Nat) : Int := xLo k alpha gamma logs[i]! i q
  let (_, acc) := (List.range n).foldl (fun (st : Int × Int) m =>
    let (xa, acc) := st
    let i := i0 + m
    let xb := xAt (i + 1)
    if i == 0 then (xb, acc) else
    -- M = (X + Y)/2 rounded down; e^M lower bound
    let M := divD (xa + xb) 2
    let eM := Max.max (expPt M).lo 0
    let D := xb - xa
    let D2 := shrD (D * D) PR                           -- D² (fixed point, rounded down)
    -- 1 + D²/24
    let f1 : Int := ONE + divD D2 24
    -- κ w² / 6 = (s - 1) w² / (12 b'²) = (2k - 3) / (24 (i+1)²)   (w = 2^-q, b' = (i+1) w)
    let kap : Int := divD ((2 * (k : Int) - 3) * ONE) (24 * ((i + 1) * (i + 1) : Nat))
    let fac : Int := f1 + kap
    let term := shrD (eM * Max.max fac 0) PR
    (xb, acc + term)) (xAt i0, 0)
  -- times w = 2^-q
  shrD acc q

/-- The lower bound for `C_k` from the enclosures `L[j] ≤ log Ψ(t_j) ≤ H[j]` (`j = 1..NTV`, index 0 unused). -/
def ckLo (k dtl ntv lsub : Nat) (L H : Array Int) (logs : Array Int) : Int :=
  -- [0, t_1]: Ψ ≥ Ψ(t_1)
  let first := segLo k L[1]! piHi 0 dtl lsub logs
  let total := (List.range (ntv - 1)).foldl (fun acc j0 =>
    let j := j0 + 1
    -- (i) value at t_{j+1}
    let c1 := segLo k L[j + 1]! piHi j dtl lsub logs
    -- (ii) left extended secant through (t_{j-1}, t_j), for t ≥ t_j
    let c2 : Int :=
      if 2 ≤ j then
        let sig : Int := (L[j]! - H[j - 1]!) * 2 ^ dtl          -- exact (slope lower bound)
        if sig < piLo then
          let alpha := L[j]! - divU (sig * j) (2 ^ dtl)
          segLo k alpha (piHi - sig) j dtl lsub logs
        else 0
      else 0
    -- (iii) right extended secant through (t_{j+1}, t_{j+2}), for t ≤ t_{j+1}
    let c3 : Int :=
      if j + 2 ≤ ntv then
        let sig : Int := (H[j + 2]! - L[j + 1]!) * 2 ^ dtl      -- exact (slope upper bound)
        if sig < piLo then
          let alpha := L[j + 1]! - divU (sig * (j + 1)) (2 ^ dtl)
          segLo k alpha (piHi - sig) j dtl lsub logs
        else 0
      else 0
    acc + Max.max c1 (Max.max c2 c3)) first
  shrD total 1

/-- `log(i 2^-q)` lower bounds for `i = 0..n` (index 0 unused). -/
def logTable (n q : Nat) : Array Int :=
  (Array.range (n + 1)).map fun i => if i == 0 then 0 else logScaled true i q

end W2C
