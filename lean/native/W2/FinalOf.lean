/-
The window-2 bound `W2Bound` (version 2 of the paper, Section 4: `Σ_{k=6}^{30} C_k ≥ 0.0026853042`) from the proof modules
(as `Prop`s: the table soundness pieces T1-T8 and `TableSoundOf`, the t-integral `TIntBound`) and the three
computational checks of the production run (claims checked against both directed recursions, the t-integral of the
claims, the nondegeneracy of the tables), which `W2/Final.lean` supplies by `native_decide`.
-/
import W2.Assembly
import W2.EntryBoundPf
import W2Prod.Claims
import BHH.StatementV2

open MeasureTheory Set Real
open scoped ENNReal

noncomputable section

namespace BHH.W2

open W2C BHH.Cert BHH

lemma meanA1_nonneg {r1 r2 : ℝ} (h0 : 0 ≤ r1) (h12 : r1 < r2) : 0 ≤ meanA1 r1 r2 := by
  unfold meanA1
  apply mul_nonneg (div_nonneg (by norm_num) (by nlinarith))
  apply intervalIntegral.integral_nonneg h12.le
  intro r hr
  exact mul_nonneg (A1c_nonneg (h0.trans hr.1)) (h0.trans hr.1)

/-- `euHi ≥ 0` for every ring of a run (so the first-step exponents are `≥ 0`). -/
lemma hub_of (hRS : RingSound) {g : Grid} (hN1 : 0 < g.N1) (hN2 : 0 < g.N2) (hNT : 2 ≤ g.NT) (hNS : 0 < g.NSUB)
    (hr : ∀ j, j < g.NR → ringOK g j = true) (dtl : ℕ) :
    ∀ ir : ℕ, 0 ≤ ubInt (mkRunData g dtl true).rings[ir]!.euHi dtl := by
  intro ir
  apply ubInt_nonneg _ dtl
  by_cases h : ir < g.NR
  · rw [mkRunData_rings, rings_getElem g h]
    have hrok := hr ir h
    simp only [ringOK, Bool.and_eq_true, decide_eq_true_eq] at hrok
    obtain ⟨-, -, -, -, -, -, hhi, -⟩ := hRS g hN1 hN2 hNT hNS ir h hrok.1 hrok.2
    exact fx_nonneg_iff.mp ((meanA1_nonneg (GridR.rad_nonneg (gR g) ir) (rad_lt (gR g) hN1 hN2 ir)).trans hhi)
  · rw [getElem!_neg _ _ (by rw [mkRunData_rings]; simp; omega)]
    exact le_rfl

/-- The eight shards together check every claim. -/
theorem claimsChecked_of_shards
    (h0 : shardOK prod.grid prod.dtl prod.kmax true (prod.claims.filter fun c => c.1 % 8 == 0) = true)
    (h1 : shardOK prod.grid prod.dtl prod.kmax true (prod.claims.filter fun c => c.1 % 8 == 1) = true)
    (h2 : shardOK prod.grid prod.dtl prod.kmax true (prod.claims.filter fun c => c.1 % 8 == 2) = true)
    (h3 : shardOK prod.grid prod.dtl prod.kmax true (prod.claims.filter fun c => c.1 % 8 == 3) = true)
    (h4 : shardOK prod.grid prod.dtl prod.kmax true (prod.claims.filter fun c => c.1 % 8 == 4) = true)
    (h5 : shardOK prod.grid prod.dtl prod.kmax true (prod.claims.filter fun c => c.1 % 8 == 5) = true)
    (h6 : shardOK prod.grid prod.dtl prod.kmax true (prod.claims.filter fun c => c.1 % 8 == 6) = true)
    (h7 : shardOK prod.grid prod.dtl prod.kmax true (prod.claims.filter fun c => c.1 % 8 == 7) = true) :
    ClaimsChecked prod.grid prod.dtl prod.kmax prod.claims := by
  intro c hc
  have key : ∀ r : ℕ, c.1 % 8 = r →
      shardOK prod.grid prod.dtl prod.kmax true (prod.claims.filter fun c => c.1 % 8 == r) = true →
      checkClaims prod.kmax
        (runT4 prod.grid (mkRunData prod.grid prod.dtl true).rings (mkRunData prod.grid prod.dtl true).tab
          (mkRunData prod.grid prod.dtl true).e1lo mkPassTab true c.1 prod.dtl prod.kmax).toArray
        (runT4 prod.grid (mkRunData prod.grid prod.dtl true).rings (mkRunData prod.grid prod.dtl true).tab
          (mkRunData prod.grid prod.dtl true).e1hi mkPassTab false c.1 prod.dtl prod.kmax).toArray c = true := by
    intro r hr hs
    exact shardOK_spec hs c (List.mem_filter.mpr ⟨hc, by simp [hr]⟩)
  have : c.1 % 8 = 0 ∨ c.1 % 8 = 1 ∨ c.1 % 8 = 2 ∨ c.1 % 8 = 3 ∨ c.1 % 8 = 4 ∨ c.1 % 8 = 5 ∨
      c.1 % 8 = 6 ∨ c.1 % 8 = 7 := by omega
  rcases this with h | h | h | h | h | h | h | h
  · exact key 0 h h0
  · exact key 1 h h1
  · exact key 2 h h2
  · exact key 3 h h3
  · exact key 4 h h4
  · exact key 5 h h5
  · exact key 6 h h6
  · exact key 7 h h7

/-- `W2Bound` from the proof modules and the computational checks of the production run. -/
theorem w2_bound_of (hRS : RingSound) (hAS : AngleSound) (hAR : AngleRange) (hFS : FrangeSound) (hDS : DistSound)
    (hA1 : A1Radial) (hA2 : A2Union) (hA2le : A2LeA1) (hPM : PairMean) (hRot : RotA2) (hSC : SectorCen)
    (hTSO : TableSoundOf) (hT : TIntBound)
    (hcc : ClaimsChecked prod.grid prod.dtl prod.kmax prod.claims)
    (htint : tintOK prod.dtl prod.T prod.kmax 8 prod.claims 26853042 (10 ^ 10) = true)
    (hnd : nondegOK prod.grid = true) : W2Bound := by
  intro hG hV
  have hN1 : 0 < prod.grid.N1 := by decide
  have hN2 : 0 < prod.grid.N2 := by decide
  have hNT : 2 ≤ prod.grid.NT := by decide
  have hNT30 : prod.grid.NT ≤ 2 ^ 30 := by decide
  have hNS : 0 < prod.grid.NSUB := by decide
  obtain ⟨hr, -⟩ := nondeg_spec hnd
  have hEB := entryBound_of hV hG hRS hAS hAR hFS hDS hA1 hA2 hA2le hPM hSC hN1 hN2 hNT hNT30 hNS hnd
  have hTS := hTSO hG hRS hAS hAR hFS hA1 hRot prod.grid prod.dtl hN1 hN2 hNT hNT30 hNS hr hEB
  have hub := hub_of hRS hN1 hN2 hNT hNS hr prod.dtl
  have h := sum_C_ge hT (g := prod.grid) (by decide) (by decide) hcc htint hTS hub (by decide)
  have e1 : ((26853042 : ℕ) : ℝ) / ((10 ^ 10 : ℕ) : ℝ) = 26853042 / 10 ^ 10 := by norm_num
  rw [e1] at h
  exact h

end BHH.W2
