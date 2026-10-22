/-
Module C: Lemma 3.5 (event bound) and the integration step of Prop 3.6.
-/
import BHH.Box.Props

open MeasureTheory Set Real
open scoped ENNReal

noncomputable section

namespace BHH

/-- Lemma 3.5 -/
theorem eventBoundProp : EventBoundProp := by
  intro m Q F f q fmin fmax Vs hQ hF hFQ hQt hq hmin hmax hvF hfmin hfmax hint
  set v := (volume Q).toReal with hvdef
  have hv0 : 0 ≤ v := ENNReal.toReal_nonneg
  have hvQ : volume Q = ENNReal.ofReal v := (ENNReal.ofReal_toReal hQt).symm
  have hFt : volume F ≠ ⊤ := ne_top_of_le_ne_top hQt (measure_mono hFQ)
  -- part 1: `∫⁻_F f ≥ fmin · vol F ≥ v q fmin`
  have h1 : ENNReal.ofReal (v * (q * fmin)) ≤ ∫⁻ x in F, f x := by
    calc ENNReal.ofReal (v * (q * fmin)) = ENNReal.ofReal fmin * ENNReal.ofReal (q * v) := by
          rw [← ENNReal.ofReal_mul hmin]; ring_nf
      _ ≤ ENNReal.ofReal fmin * volume F := mul_le_mul_right hvF _
      _ = ∫⁻ x in F, ENNReal.ofReal fmin := (setLIntegral_const F _).symm
      _ ≤ ∫⁻ x in F, f x := setLIntegral_mono' hF fun x hx => hfmin x (hFQ hx)
  -- part 2: `∫⁻_F f ≥ ∫⁻_Q f - fmax vol(Q \ F)`
  have h2 : ENNReal.ofReal (v * (Vs - (1 - q) * fmax)) ≤ ∫⁻ x in F, f x := by
    rcases eq_or_lt_of_le hv0 with hv | hv
    · rw [← hv, zero_mul, ENNReal.ofReal_zero]; exact zero_le
    have hq1 : q ≤ 1 := by
      have : ENNReal.ofReal (q * v) ≤ ENNReal.ofReal v := hvF.trans (hvQ ▸ measure_mono hFQ)
      rw [ENNReal.ofReal_le_ofReal_iff hv0] at this
      nlinarith
    have hdiff : volume (Q \ F) ≤ ENNReal.ofReal ((1 - q) * v) := by
      rw [measure_sdiff hFQ hF.nullMeasurableSet hFt, hvQ]
      calc ENNReal.ofReal v - volume F ≤ ENNReal.ofReal v - ENNReal.ofReal (q * v) := tsub_le_tsub_left hvF _
        _ = ENNReal.ofReal (v - q * v) := (ENNReal.ofReal_sub _ (by positivity)).symm
        _ = ENNReal.ofReal ((1 - q) * v) := by ring_nf
    have hsplit : ∫⁻ x in Q, f x = (∫⁻ x in F, f x) + ∫⁻ x in Q \ F, f x := by
      rw [← lintegral_inter_add_sdiff f Q hF, Set.inter_eq_right.2 hFQ]
    have hrest : ∫⁻ x in Q \ F, f x ≤ ENNReal.ofReal ((1 - q) * fmax * v) := by
      calc ∫⁻ x in Q \ F, f x ≤ ∫⁻ x in Q \ F, ENNReal.ofReal fmax :=
            setLIntegral_mono' (hQ.diff hF) fun x hx => hfmax x hx.1
        _ = ENNReal.ofReal fmax * volume (Q \ F) := setLIntegral_const _ _
        _ ≤ ENNReal.ofReal fmax * ENNReal.ofReal ((1 - q) * v) := mul_le_mul_right hdiff _
        _ = ENNReal.ofReal ((1 - q) * fmax * v) := by
          rw [← ENNReal.ofReal_mul hmax]; ring_nf
    have hge : ENNReal.ofReal (v * Vs) ≤ (∫⁻ x in F, f x) + ENNReal.ofReal ((1 - q) * fmax * v) := by
      rw [hsplit] at hint; exact hint.trans (add_le_add le_rfl hrest)
    calc ENNReal.ofReal (v * (Vs - (1 - q) * fmax))
        = ENNReal.ofReal (v * Vs - (1 - q) * fmax * v) := by ring_nf
      _ = ENNReal.ofReal (v * Vs) - ENNReal.ofReal ((1 - q) * fmax * v) :=
          ENNReal.ofReal_sub _ (by have : 0 ≤ 1 - q := by linarith
                                   positivity)
      _ ≤ ∫⁻ x in F, f x := tsub_le_iff_right.2 hge
  rw [mul_max_of_nonneg _ _ hv0, ENNReal.ofReal_max]
  exact max_le h1 h2

/-- superadditivity of the lower Lebesgue integral over a finite sum -/
lemma le_lintegral_finset_sum {α ι : Type*} [MeasurableSpace α] {μ : Measure α} (S : Finset ι)
    (g : ι → α → ℝ≥0∞) : ∑ σ ∈ S, ∫⁻ x, g σ x ∂μ ≤ ∫⁻ x, ∑ σ ∈ S, g σ x ∂μ := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert σ S hσ ih =>
    rw [Finset.sum_insert hσ]
    simp_rw [Finset.sum_insert hσ]
    exact (add_le_add le_rfl ih).trans (le_lintegral_add _ _)

/-- the integration step of Prop 3.6 -/
theorem partitionBoundProp : PartitionBoundProp := by
  intro m ι S Q F f G g0 w hQ hF hFQ hg0 hw hG
  -- pointwise lower bound for the integrand on `Q`
  have hpt : ∀ x ∈ Q, ENNReal.ofReal g0 * f x + ∑ σ ∈ S, ENNReal.ofReal (w σ) * (F σ).indicator f x ≤
      ENNReal.ofReal (G x) * f x := by
    intro x hx
    have hsum : ENNReal.ofReal (g0 + ∑ σ ∈ S, w σ * (F σ).indicator (fun _ => (1 : ℝ)) x) =
        ENNReal.ofReal g0 + ∑ σ ∈ S, ENNReal.ofReal (w σ * (F σ).indicator (fun _ => (1 : ℝ)) x) := by
      rw [ENNReal.ofReal_add hg0 (Finset.sum_nonneg fun σ hσ => mul_nonneg (hw σ hσ)
        (Set.indicator_nonneg (fun _ _ => zero_le_one) _)),
        ENNReal.ofReal_sum_of_nonneg fun σ hσ => mul_nonneg (hw σ hσ)
        (Set.indicator_nonneg (fun _ _ => zero_le_one) _)]
    have hterm : ∀ σ ∈ S, ENNReal.ofReal (w σ * (F σ).indicator (fun _ => (1 : ℝ)) x) * f x =
        ENNReal.ofReal (w σ) * (F σ).indicator f x := by
      intro σ _
      by_cases hxσ : x ∈ F σ
      · simp [Set.indicator_of_mem hxσ]
      · simp [Set.indicator_of_notMem hxσ]
    calc ENNReal.ofReal g0 * f x + ∑ σ ∈ S, ENNReal.ofReal (w σ) * (F σ).indicator f x
        = (ENNReal.ofReal g0 + ∑ σ ∈ S, ENNReal.ofReal (w σ * (F σ).indicator (fun _ => (1 : ℝ)) x)) *
            f x := by
          rw [add_mul, Finset.sum_mul, Finset.sum_congr rfl hterm]
      _ = ENNReal.ofReal (g0 + ∑ σ ∈ S, w σ * (F σ).indicator (fun _ => (1 : ℝ)) x) * f x := by
          rw [hsum]
      _ ≤ ENNReal.ofReal (G x) * f x := mul_le_mul_left (ENNReal.ofReal_le_ofReal (hG x hx)) _
  have hind : ∀ σ ∈ S, ∫⁻ x in Q, (F σ).indicator f x = ∫⁻ x in F σ, f x := by
    intro σ hσ
    rw [lintegral_indicator (hF σ hσ), Measure.restrict_restrict (hF σ hσ),
      Set.inter_eq_left.2 (hFQ σ hσ)]
  calc ENNReal.ofReal g0 * (∫⁻ x in Q, f x) + ∑ σ ∈ S, ENNReal.ofReal (w σ) * ∫⁻ x in F σ, f x
      = (∫⁻ x in Q, ENNReal.ofReal g0 * f x) +
          ∑ σ ∈ S, ∫⁻ x in Q, ENNReal.ofReal (w σ) * (F σ).indicator f x := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        congr 1
        refine Finset.sum_congr rfl fun σ hσ => ?_
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, hind σ hσ]
    _ ≤ (∫⁻ x in Q, ENNReal.ofReal g0 * f x) +
          ∫⁻ x in Q, ∑ σ ∈ S, ENNReal.ofReal (w σ) * (F σ).indicator f x :=
        add_le_add le_rfl (le_lintegral_finset_sum S _)
    _ ≤ ∫⁻ x in Q, (ENNReal.ofReal g0 * f x + ∑ σ ∈ S, ENNReal.ofReal (w σ) * (F σ).indicator f x) :=
        le_lintegral_add _ _
    _ ≤ ∫⁻ x in Q, ENNReal.ofReal (G x) * f x := setLIntegral_mono' hQ hpt

end BHH
