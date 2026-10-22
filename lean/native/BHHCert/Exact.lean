/-
Exact fixed-point interval arithmetic for the rigorous leaf bounds (core Lean only).

Numbers are integers `n` standing for `n / 2^PR`.  An interval `⟨lo, hi⟩` stands for
`[lo / 2^PR, hi / 2^PR]`.  Every operation rounds outward.  Everything here is written so that the Lean
kernel can evaluate it (`decide +kernel`, track K): structural recursion only (fuel where needed), Int/Nat
arithmetic only (GMP-accelerated literals in the kernel), no Float, no Array, no well-founded recursion.
The compiled version of the same code is used by track N (`native_decide`).

Results that come from an unverified search (square roots by Newton's method, candidate angles) are
always checked by a cheap exact test before use; the soundness proofs (BHH/Ivl/*) rely only on the tests.
-/

namespace BHH.Cert

/-- Fraction bits of the fixed point. -/
def PR : Nat := 96

/-- `2^PR` -/
def ONE : Int := 79228162514264337593543950336

/-- floor(a / 2^n) -/
@[inline] def shrD (a : Int) (n : Nat) : Int := a >>> n
/-- ceil(a / 2^n) -/
@[inline] def shrU (a : Int) (n : Nat) : Int := -((-a) >>> n)
/-- floor(a / b) for b > 0 -/
@[inline] def divD (a b : Int) : Int := a / b
/-- ceil(a / b) for b > 0 -/
@[inline] def divU (a b : Int) : Int := -((-a) / b)

/-! ## integer square roots (Newton, then checked) -/

/-- Newton iteration for the floor square root, started above `√n`. -/
def isqrtGo (n : Nat) : Nat → Nat → Nat
  | 0, x => x
  | fuel + 1, x =>
    let y := (x + n / x) / 2
    if y < x then isqrtGo n fuel y else x

/-- Candidate floor square root (unverified). -/
def isqrtCand (n : Nat) : Nat :=
  if n ≤ 1 then n else isqrtGo n 200 (2 ^ (Nat.log2 n / 2 + 1))

/-- A number `r` with `r * r ≤ n` (checked; `0` if the check fails). -/
def isqrtLo (n : Nat) : Nat :=
  let r := isqrtCand n
  if r * r ≤ n then r else 0

/-- A number `r` with `n ≤ r * r` (checked; `n + 1` as fallback). -/
def isqrtHi (n : Nat) : Nat :=
  let r := isqrtCand n
  if n ≤ r * r then r else if n ≤ (r + 1) * (r + 1) then r + 1 else n + 1

/-! ## intervals -/

/-- The interval `[lo / 2^PR, hi / 2^PR]`. -/
structure Iv where
  lo : Int
  hi : Int
  deriving Repr, Inhabited, BEq

namespace Iv

/-- the exact number `n / 2^PR` -/
@[inline] def pt (n : Int) : Iv := ⟨n, n⟩
/-- the exact integer `n` -/
@[inline] def int (n : Int) : Iv := ⟨n * ONE, n * ONE⟩
/-- the exact dyadic `n / 2^e` with `e ≤ PR` -/
@[inline] def dy (n : Int) (e : Nat) : Iv := let v := n * 2 ^ (PR - e); ⟨v, v⟩

@[inline] def add (a b : Iv) : Iv := ⟨a.lo + b.lo, a.hi + b.hi⟩
@[inline] def sub (a b : Iv) : Iv := ⟨a.lo - b.hi, a.hi - b.lo⟩
@[inline] def neg (a : Iv) : Iv := ⟨-a.hi, -a.lo⟩

/-- product (general signs) -/
def mul (a b : Iv) : Iv :=
  if 0 ≤ a.lo then
    if 0 ≤ b.lo then ⟨shrD (a.lo * b.lo) PR, shrU (a.hi * b.hi) PR⟩
    else if b.hi ≤ 0 then ⟨shrD (a.hi * b.lo) PR, shrU (a.lo * b.hi) PR⟩
    else ⟨shrD (a.hi * b.lo) PR, shrU (a.hi * b.hi) PR⟩
  else if a.hi ≤ 0 then
    if 0 ≤ b.lo then ⟨shrD (a.lo * b.hi) PR, shrU (a.hi * b.lo) PR⟩
    else if b.hi ≤ 0 then ⟨shrD (a.hi * b.hi) PR, shrU (a.lo * b.lo) PR⟩
    else ⟨shrD (a.lo * b.hi) PR, shrU (a.lo * b.lo) PR⟩
  else
    if 0 ≤ b.lo then ⟨shrD (a.lo * b.hi) PR, shrU (a.hi * b.hi) PR⟩
    else if b.hi ≤ 0 then ⟨shrD (a.hi * b.lo) PR, shrU (a.lo * b.lo) PR⟩
    else ⟨shrD (min (a.lo * b.hi) (a.hi * b.lo)) PR, shrU (max (a.lo * b.lo) (a.hi * b.hi)) PR⟩

/-- square -/
def sqr (a : Iv) : Iv :=
  if 0 ≤ a.lo then ⟨shrD (a.lo * a.lo) PR, shrU (a.hi * a.hi) PR⟩
  else if a.hi ≤ 0 then ⟨shrD (a.hi * a.hi) PR, shrU (a.lo * a.lo) PR⟩
  else ⟨0, shrU (max (a.lo * a.lo) (a.hi * a.hi)) PR⟩

/-- product with a natural number -/
@[inline] def mulNat (a : Iv) (n : Nat) : Iv := ⟨a.lo * n, a.hi * n⟩
/-- quotient by a positive natural number -/
@[inline] def divNat (a : Iv) (n : Nat) : Iv := ⟨divD a.lo n, divU a.hi n⟩
/-- multiplication by `2^e` -/
@[inline] def mul2e (a : Iv) (e : Nat) : Iv := ⟨a.lo * 2 ^ e, a.hi * 2 ^ e⟩
/-- division by `2^e` -/
@[inline] def div2e (a : Iv) (e : Nat) : Iv := ⟨shrD a.lo e, shrU a.hi e⟩

/-- reciprocal of a positive interval (`b.lo > 0` required; otherwise a useless interval) -/
def inv (b : Iv) : Iv :=
  if 0 < b.lo then ⟨divD (ONE * ONE) b.hi, divU (ONE * ONE) b.lo⟩ else ⟨-1, 1⟩

/-- quotient with a positive denominator interval -/
def div (a b : Iv) : Iv :=
  if 0 < b.lo then
    let lo := if 0 ≤ a.lo then divD (a.lo * ONE) b.hi else divD (a.lo * ONE) b.lo
    let hi := if 0 ≤ a.hi then divU (a.hi * ONE) b.lo else divU (a.hi * ONE) b.hi
    ⟨lo, hi⟩
  else ⟨-1, 1⟩

/-- square root (negative parts clipped to 0) -/
def sqrt (a : Iv) : Iv :=
  let lo := if a.lo ≤ 0 then 0 else (isqrtLo (a.lo * ONE).toNat : Int)
  let hi := if a.hi ≤ 0 then 0 else (isqrtHi (a.hi * ONE).toNat : Int)
  ⟨lo, hi⟩

@[inline] def min (a b : Iv) : Iv := ⟨Min.min a.lo b.lo, Min.min a.hi b.hi⟩
@[inline] def max (a b : Iv) : Iv := ⟨Max.max a.lo b.lo, Max.max a.hi b.hi⟩
/-- absolute value -/
def abs (a : Iv) : Iv :=
  if 0 ≤ a.lo then a else if a.hi ≤ 0 then neg a else ⟨0, Max.max (-a.lo) a.hi⟩
/-- the union hull -/
@[inline] def hull (a b : Iv) : Iv := ⟨Min.min a.lo b.lo, Max.max a.hi b.hi⟩
/-- widen by `e / 2^PR` on both sides -/
@[inline] def widen (a : Iv) (e : Int) : Iv := ⟨a.lo - e, a.hi + e⟩

end Iv

/-! ## π -/

/-- `piLo / 2^PR < π < piHi / 2^PR` (from Mathlib's `Real.pi_gt_d20`, `Real.pi_lt_d20`). -/
def piLo : Int := 248902613312231085230312514221
def piHi : Int := 248902613312231085231104795848
def piIv : Iv := ⟨piLo, piHi⟩
/-- `piHi - piLo` -/
def piErr : Int := piHi - piLo

/-! ## sine and cosine at an exact point -/

/-- Taylor terms `T_m = s^m / m!` for `s = t / 2^(PR + r)`, as intervals.  Invariant: `term ∋ T_m`, and
`c`, `s` hold the partial sums of `cos s`, `sin s` over the indices `< m`.  Stops at `m = n` and returns
`(c, s, T_n)`.  Out of fuel (not reached with fuel `n + 1` from `m = 0`): a trivially valid answer. -/
def taylorGo (t : Int) (r n : Nat) : Nat → Nat → Iv → Iv → Iv → Iv × Iv × Iv
  | 0, _, _, _, _ => (⟨-4 * ONE, 4 * ONE⟩, ⟨-4 * ONE, 4 * ONE⟩, ⟨0, 0⟩)
  | fuel + 1, m, term, c, s =>
    if m == n then (c, s, term) else
    let c' := if m % 4 == 0 then Iv.add c term else if m % 4 == 2 then Iv.sub c term else c
    let s' := if m % 4 == 1 then Iv.add s term else if m % 4 == 3 then Iv.sub s term else s
    let numLo := if 0 ≤ t then term.lo * t else term.hi * t
    let numHi := if 0 ≤ t then term.hi * t else term.lo * t
    let nt : Iv := ⟨divD (shrD numLo (PR + r)) (m + 1), divU (shrU numHi (PR + r)) (m + 1)⟩
    taylorGo t r n fuel (m + 1) nt c' s'

/-- Number of Taylor terms. -/
def NTERMS : Nat := 26

/-- Enclosures of `cos s`, `sin s` for `s = t / 2^(PR + r)`, `|s| ≤ 1`, by the Taylor polynomials over the
indices `< NTERMS` and the remainder bound `|s|^n (n+1)/(n! n)` (Mathlib `Complex.exp_bound`). -/
def sinCosSmall (t : Int) (r : Nat) : Iv × Iv :=
  let (c, s, last) := taylorGo t r NTERMS (NTERMS + 1) 0 (Iv.int 1) ⟨0, 0⟩ ⟨0, 0⟩
  let mag := Max.max (Int.natAbs last.lo) (Int.natAbs last.hi)
  let rem : Int := divU (mag * (NTERMS + 1)) NTERMS + 1
  (Iv.widen c rem, Iv.widen s rem)

/-- doubling: from `(cos x, sin x)` to `(cos 2x, sin 2x)` -/
def dbl (cs : Iv × Iv) : Iv × Iv :=
  let (c, s) := cs
  (Iv.sub (Iv.int 1) (Iv.mul2e (Iv.sqr s) 1), Iv.mul2e (Iv.mul s c) 1)

def dblN : Nat → Iv × Iv → Iv × Iv
  | 0, cs => cs
  | n + 1, cs => dblN n (dbl cs)

/-- clip an enclosure of a sine or cosine to `[-1, 1]` -/
def clip1 (a : Iv) : Iv := ⟨Max.max a.lo (-ONE), Min.min a.hi ONE⟩

/-- Enclosures of `(cos x, sin x)` for the exact point `x = t / 2^PR` with `|x| ≤ 8`
(`(⟨-1,1⟩, ⟨-1,1⟩)` otherwise). -/
def cosSin (t : Int) : Iv × Iv :=
  if t.natAbs ≤ 8 * ONE.toNat then
    let (c, s) := dblN 4 (sinCosSmall t 4)
    (clip1 c, clip1 s)
  else (⟨-ONE, ONE⟩, ⟨-ONE, ONE⟩)

end BHH.Cert
