/-
Candidate arc endpoints from Float (track N only; never trusted, every candidate is certified).
-/
import BHHCert.Leaf

namespace BHH.Cert

/-- `2^-PR` as a Float -/
def fScale : Float := Float.scaleB 1.0 (-96)

/-- Float value of a fixed-point integer (approximate). -/
def fixToFloat (n : Int) : Float := Float.ofInt n * fScale

/-- Fixed-point integer near the Float `x` (|x| < 2^10): round(x * 2^52) * 2^44. -/
def floatToFix (x : Float) : Int := (x * 4503599627370496.0).round.toInt64.toInt * 2 ^ (PR - 52)

/-- Candidates `ψ ∓ α`, `ψ = atan2(wy, wx)`, `α = acos(√d2 / (2R))`. -/
def floatCand : CandFn := fun wx wy d2 R =>
  let fx := fixToFloat wx
  let fy := fixToFloat wy
  let d := Float.sqrt (fx * fx + fy * fy)
  let fR := fixToFloat R
  let psi := Float.atan2 fy fx
  let x := d / (2 * fR)
  let al := Float.acos (if x > 1 then 1 else x)
  let _ := d2
  (floatToFix (psi - al), floatToFix (psi + al))

end BHH.Cert

namespace BHH.Cert

/-- Candidate `arcsin` from Float (track N; never trusted). -/
def floatAsin : AsinFn := fun x =>
  let fx := fixToFloat x
  floatToFix (Float.asin (if fx > 1 then 1 else if fx < -1 then -1 else fx))

end BHH.Cert
