import BHH.MainN3
import W3.Assembly

/-! Theorem 1.1 of the paper (native proof), from `MainBoundsV3` (k = 3, 4, 5) and a window-3 bound `W3BoundAt w`
(6 ≤ k ≤ 22), which is a hypothesis here. -/

namespace BHH

/-- any window-3 constant `w ≥ 0` and any `b ≤ 5/8 + C_3 + C_4 + C_5 + w` (the certified values) -/
theorem betaBoundV3At_N_of {w b : ℝ} (hw : 0 ≤ w)
    (hb : b ≤ 5 / 8 + 117130195 / 10 ^ 10 + 63707166 / 10 ^ 10 + 35280362 / 10 ^ 10 + w) (hW : W3BoundAt w) :
    BetaBoundV3At b :=
  W3.betaBoundV3At_of hw hb mainBoundsV3_N hW

theorem bhhBetaBoundV3At_N_of {w b : ℝ} (hw : 0 ≤ w)
    (hb : b ≤ 5 / 8 + 117130195 / 10 ^ 10 + 63707166 / 10 ^ 10 + 35280362 / 10 ^ 10 + w) (hW : W3BoundAt w) :
    BHHBetaBoundV3At b :=
  W3.bhhBetaBoundV3At_of (betaBoundV3At_N_of hw hb hW)

/-- the paper's constants (grid (60,30,144)) -/
theorem betaBoundV3_N_of (hW : W3Bound) : BetaBoundV3 :=
  W3.betaBoundV3_of mainBoundsV3_N hW

theorem bhhBetaBoundV3_N_of (hW : W3Bound) : BHHBetaBoundV3 :=
  W3.bhhBetaBoundV3_of (betaBoundV3_N_of hW)

end BHH
