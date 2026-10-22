/-
Module C: the distribution function of a difference of independent uniform variables (`cdfR`, point masses allowed).
-/
import BHH.Box.Uniform
import BHH.Box.Props

open MeasureTheory Set Real Filter Topology
open scoped ENNReal

noncomputable section

namespace BHH

/-! ## `∫ ramp(K - s) ds` -/

lemma ramp_nonneg (t : ℝ) : 0 ≤ ramp t := le_max_right _ _

lemma continuous_ramp : Continuous ramp := continuous_id.max continuous_const

/-- `(ramp u)²/2` has derivative `ramp u` -/
lemma hasDerivAt_rampSq (u : ℝ) : HasDerivAt (fun v => ramp v ^ 2 / 2) (ramp u) u := by
  rcases lt_trichotomy u 0 with hu | rfl | hu
  · have hev : (fun v => ramp v ^ 2 / 2) =ᶠ[𝓝 u] fun _ => 0 := by
      filter_upwards [Iio_mem_nhds hu] with v hv
      simp [ramp, max_eq_right (show v < 0 from hv).le]
    rw [show ramp u = 0 from max_eq_right hu.le]
    exact (hasDerivAt_const u (0 : ℝ)).congr_of_eventuallyEq hev
  · rw [hasDerivAt_iff_isLittleO]
    have e : (fun x' : ℝ => ramp x' ^ 2 / 2 - ramp 0 ^ 2 / 2 - (x' - 0) • ramp 0) = fun x' => ramp x' ^ 2 / 2 := by
      funext x'; simp [ramp]
    rw [e]
    simp only [sub_zero]
    refine Asymptotics.IsBigO.trans_isLittleO ?_ (Asymptotics.isLittleO_pow_id (𝕜 := ℝ) one_lt_two)
    refine Asymptotics.IsBigO.of_bound 1 (Eventually.of_forall fun v => ?_)
    simp only [Real.norm_eq_abs, one_mul]
    rw [abs_of_nonneg (div_nonneg (sq_nonneg (ramp v)) zero_le_two), abs_of_nonneg (sq_nonneg v)]
    unfold ramp
    rcases le_total v 0 with hv | hv
    · rw [max_eq_right hv]; nlinarith [sq_nonneg v]
    · rw [max_eq_left hv]; linarith [sq_nonneg v]
  · have hev : (fun v => ramp v ^ 2 / 2) =ᶠ[𝓝 u] fun v => v ^ 2 / 2 := by
      filter_upwards [Ioi_mem_nhds hu] with v hv
      simp [ramp, max_eq_left (show 0 < v from hv).le]
    rw [show ramp u = u from max_eq_left hu.le]
    have h := ((hasDerivAt_id' u).pow 2).div_const 2
    have h' : HasDerivAt (fun v => v ^ 2 / 2) u u := by
      convert h using 1; push_cast; ring
    exact h'.congr_of_eventuallyEq hev

lemma continuous_ramp_sub (K : ℝ) : Continuous fun s => ramp (K - s) :=
  continuous_ramp.comp (continuous_const.sub continuous_id)

lemma integral_ramp_sub (K a b : ℝ) :
    ∫ s in a..b, ramp (K - s) = (ramp (K - a) ^ 2 - ramp (K - b) ^ 2) / 2 := by
  have hd : ∀ s ∈ uIcc a b, HasDerivAt (fun s => -(ramp (K - s) ^ 2 / 2)) (ramp (K - s)) s := by
    intro s _
    have h1 : HasDerivAt (fun s => ramp (K - s) ^ 2 / 2) (ramp (K - s) * (-1)) s :=
      (hasDerivAt_rampSq (K - s)).comp s ((hasDerivAt_id' s).const_sub K)
    have h2 := h1.neg
    simp only [mul_neg, mul_one, neg_neg] at h2
    exact h2
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd ((continuous_ramp_sub K).intervalIntegrable a b)]
  ring

/-! ## The uniform law on `[a, b]` (a point mass if `a = b`) -/

/-- uniform on `[a, b]` if `a < b`, the point mass at `a` otherwise -/
def uLaw (a b : ℝ) : Measure ℝ := if a < b then unifI a b else Measure.dirac a

lemma uLaw_isProb (a b : ℝ) : IsProbabilityMeasure (uLaw a b) := by
  unfold uLaw; split_ifs with h
  · exact unifI_isProb h
  · infer_instance

lemma uLaw_of_lt {a b : ℝ} (h : a < b) : uLaw a b = unifI a b := by simp [uLaw, h]

lemma uLaw_of_eq (a : ℝ) : uLaw a a = Measure.dirac a := by simp [uLaw]

lemma unifI_apply {a b : ℝ} {S : Set ℝ} (hS : MeasurableSet S) :
    unifI a b S = (ENNReal.ofReal (b - a))⁻¹ * volume (S ∩ Icc a b) := by
  rw [unifI, Measure.smul_apply, Measure.restrict_apply hS, smul_eq_mul]

/-- `vol([a, b] ∩ [t, ∞)) = ramp(b - t) - ramp(a - t)` -/
lemma volume_Ici_inter_Icc {a b : ℝ} (hab : a ≤ b) (t : ℝ) :
    volume (Ici t ∩ Icc a b) = ENNReal.ofReal (ramp (b - t) - ramp (a - t)) := by
  have e : Ici t ∩ Icc a b = Icc (max a t) b := by
    ext s; simp only [mem_inter_iff, mem_Ici, mem_Icc, max_le_iff]; tauto
  rw [e, Real.volume_Icc]
  unfold ramp
  rcases le_total t a with h1 | h1
  · rw [max_eq_left h1, max_eq_left (by linarith : 0 ≤ b - t), max_eq_left (by linarith : 0 ≤ a - t)]
    ring_nf
  · rcases le_total t b with h2 | h2
    · rw [max_eq_right h1, max_eq_left (by linarith : 0 ≤ b - t), max_eq_right (by linarith : a - t ≤ 0)]
      ring_nf
    · rw [max_eq_right h1, max_eq_right (by linarith : b - t ≤ 0), max_eq_right (by linarith : a - t ≤ 0),
        ENNReal.ofReal_of_nonpos (by linarith), sub_self, ENNReal.ofReal_zero]

/-- `vol([a, b] ∩ (-∞, t]) = ramp(t - a) - ramp(t - b)` -/
lemma volume_Iic_inter_Icc {a b : ℝ} (hab : a ≤ b) (t : ℝ) :
    volume (Iic t ∩ Icc a b) = ENNReal.ofReal (ramp (t - a) - ramp (t - b)) := by
  have e : Iic t ∩ Icc a b = Icc a (min b t) := by
    ext s; simp only [mem_inter_iff, mem_Iic, mem_Icc, le_min_iff]; tauto
  rw [e, Real.volume_Icc]
  unfold ramp
  rcases le_total t a with h1 | h1
  · rw [max_eq_right (by linarith : t - a ≤ 0), max_eq_right (by linarith : t - b ≤ 0), sub_self,
      ENNReal.ofReal_zero, ENNReal.ofReal_of_nonpos]
    have := min_le_right b t; linarith
  · rcases le_total t b with h2 | h2
    · rw [min_eq_right h2, max_eq_left (by linarith : 0 ≤ t - a), max_eq_right (by linarith : t - b ≤ 0)]
      ring_nf
    · rw [min_eq_left h2, max_eq_left (by linarith : 0 ≤ t - a), max_eq_left (by linarith : 0 ≤ t - b)]
      ring_nf

lemma clamp_eq {w u : ℝ} (hw : 0 < w) :
    (ramp u - ramp (u - w)) / w = min (max (u / w) 0) 1 := by
  unfold ramp
  rcases le_total u 0 with h1 | h1
  · rw [max_eq_right h1, max_eq_right (by linarith : u - w ≤ 0),
      max_eq_right (div_nonpos_of_nonpos_of_nonneg h1 hw.le)]
    simp
  · rcases le_total u w with h2 | h2
    · rw [max_eq_left h1, max_eq_right (by linarith : u - w ≤ 0), max_eq_left (div_nonneg h1 hw.le),
        min_eq_left ((div_le_one hw).2 h2)]
      ring
    · rw [max_eq_left h1, max_eq_left (by linarith : 0 ≤ u - w),
        max_eq_left (div_nonneg h1 hw.le), min_eq_right ((le_div_iff₀ hw).2 (by linarith))]
      field_simp; ring

/-! ## The distribution function of `X - Y` -/

lemma measurableSet_sub_le (z : ℝ) : MeasurableSet {p : ℝ × ℝ | p.1 - p.2 ≤ z} :=
  measurableSet_le (measurable_fst.sub measurable_snd) measurable_const

/-- `P(X - Y ≤ z) = cdfR a b c d z` for independent `X ~ uLaw a b`, `Y ~ uLaw c d` -/
theorem cdf_prod {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d) (z : ℝ) :
    ((uLaw a b).prod (uLaw c d)) {p | p.1 - p.2 ≤ z} = ENNReal.ofReal (cdfR a b c d z) := by
  rcases eq_or_lt_of_le hab with hab' | hab' <;> rcases eq_or_lt_of_le hcd with hcd' | hcd'
  · -- both point masses
    subst hab' hcd'
    rw [uLaw_of_eq, uLaw_of_eq, Measure.dirac_prod_dirac, Measure.dirac_apply' _ (measurableSet_sub_le z)]
    simp only [cdfR, and_self, ↓reduceIte, Set.indicator, Set.mem_ofPred_eq, Pi.one_apply]
    split_ifs <;> simp
  · -- `X` a point mass
    subst hab'
    have := unifI_isProb hcd'
    rw [uLaw_of_eq, uLaw_of_lt hcd', Measure.dirac_prod,
      Measure.map_apply measurable_prodMk_left (measurableSet_sub_le z)]
    have e : Prod.mk a ⁻¹' {p : ℝ × ℝ | p.1 - p.2 ≤ z} = Ici (a - z) := by
      ext t; simp only [mem_preimage, mem_ofPred_eq, mem_Ici]; constructor <;> intro h <;> linarith
    rw [e, unifI_apply measurableSet_Ici, volume_Ici_inter_Icc hcd]
    have hw : 0 < d - c := sub_pos.2 hcd'
    simp only [cdfR, hcd'.ne, and_false, ↓reduceIte]
    rw [← clamp_eq hw, ← ENNReal.ofReal_inv_of_pos hw, ← ENNReal.ofReal_mul (inv_nonneg.2 hw.le)]
    congr 1
    rw [show d - (a - z) = z + d - a by ring, show c - (a - z) = z + d - a - (d - c) by ring]
    ring
  · -- `Y` a point mass
    subst hcd'
    have := unifI_isProb hab'
    rw [uLaw_of_eq, uLaw_of_lt hab', Measure.prod_dirac,
      Measure.map_apply (by fun_prop : Measurable fun x : ℝ => (x, c)) (measurableSet_sub_le z)]
    have e : (fun x => (x, c)) ⁻¹' {p : ℝ × ℝ | p.1 - p.2 ≤ z} = Iic (z + c) := by
      ext t; simp only [mem_preimage, mem_ofPred_eq, mem_Iic]; constructor <;> intro h <;> linarith
    rw [e, unifI_apply measurableSet_Iic, volume_Iic_inter_Icc hab]
    have hw : 0 < b - a := sub_pos.2 hab'
    simp only [cdfR, hab'.ne, ↓reduceIte, and_true]
    rw [← clamp_eq hw, ← ENNReal.ofReal_inv_of_pos hw, ← ENNReal.ofReal_mul (inv_nonneg.2 hw.le)]
    congr 1
    rw [show z + c - b = z + c - a - (b - a) by ring]
    ring
  · -- both uniform
    have hP := unifI_isProb hcd'
    rw [uLaw_of_lt hab', uLaw_of_lt hcd', Measure.prod_apply (measurableSet_sub_le z)]
    have hw1 : 0 < b - a := sub_pos.2 hab'
    have hw2 : 0 < d - c := sub_pos.2 hcd'
    have e : ∀ s, Prod.mk s ⁻¹' {p : ℝ × ℝ | p.1 - p.2 ≤ z} = Ici (s - z) := by
      intro s; ext t; simp only [mem_preimage, mem_ofPred_eq, mem_Ici]; constructor <;> intro h <;> linarith
    have hinner : ∀ s, unifI c d (Prod.mk s ⁻¹' {p : ℝ × ℝ | p.1 - p.2 ≤ z}) =
        ENNReal.ofReal ((ramp (z + d - s) - ramp (z + c - s)) / (d - c)) := by
      intro s
      rw [e, unifI_apply measurableSet_Ici, volume_Ici_inter_Icc hcd, ← ENNReal.ofReal_inv_of_pos hw2,
        ← ENNReal.ofReal_mul (inv_nonneg.2 hw2.le)]
      congr 1
      rw [show d - (s - z) = z + d - s by ring, show c - (s - z) = z + c - s by ring]
      ring
    simp_rw [hinner]
    have hg0 : ∀ s, 0 ≤ (ramp (z + d - s) - ramp (z + c - s)) / (d - c) := by
      intro s
      refine div_nonneg ?_ hw2.le
      unfold ramp
      have : z + c - s ≤ z + d - s := by linarith
      exact sub_nonneg.2 (max_le_max this le_rfl)
    have hgc : Continuous fun s => (ramp (z + d - s) - ramp (z + c - s)) / (d - c) :=
      ((continuous_ramp.comp (continuous_const.sub continuous_id)).sub
        (continuous_ramp.comp (continuous_const.sub continuous_id))).div_const _
    have hgb : ∀ s, (ramp (z + d - s) - ramp (z + c - s)) / (d - c) ≤ 1 := by
      intro s
      rw [div_le_one hw2]
      unfold ramp
      rcases le_total (z + c - s) 0 with h1 | h1
      · rw [max_eq_right h1, sub_zero]
        rcases le_total (z + d - s) 0 with h2 | h2
        · rw [max_eq_right h2]; linarith
        · rw [max_eq_left h2]; linarith
      · rw [max_eq_left h1, max_eq_left (by linarith : 0 ≤ z + d - s)]; linarith
    have hint : Integrable (fun s => (ramp (z + d - s) - ramp (z + c - s)) / (d - c)) (unifI a b) := by
      have := unifI_isProb hab'
      refine Integrable.mono' (integrable_const (1 : ℝ)) hgc.aestronglyMeasurable
        (Eventually.of_forall fun s => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (hg0 s)]; exact hgb s
    rw [← ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall hg0), integral_unifI hab']
    congr 1
    rw [intervalIntegral.integral_div, intervalIntegral.integral_sub
      ((continuous_ramp_sub _).intervalIntegrable a b) ((continuous_ramp_sub _).intervalIntegrable a b),
      integral_ramp_sub, integral_ramp_sub]
    simp only [cdfR, hab'.ne, hcd'.ne, ↓reduceIte, and_false]
    field_simp
    ring

/-- the law of `X - Y` has no atoms if one of the two intervals is not a point -/
theorem prod_sub_eq_null {a b c d : ℝ} (h : a < b ∨ c < d) (z : ℝ) :
    ((uLaw a b).prod (uLaw c d)) {p | p.1 - p.2 = z} = 0 := by
  have hm : MeasurableSet {p : ℝ × ℝ | p.1 - p.2 = z} :=
    measurableSet_eq_fun (measurable_fst.sub measurable_snd) measurable_const
  have hP1 := uLaw_isProb a b
  have hP2 := uLaw_isProb c d
  rcases h with h | h
  · -- integrate over `Y` first
    rw [Measure.prod_apply_symm hm]
    have h0 : ∀ t, uLaw a b ((fun x => (x, t)) ⁻¹' {p : ℝ × ℝ | p.1 - p.2 = z}) = 0 := by
      intro t
      have e : (fun x => (x, t)) ⁻¹' {p : ℝ × ℝ | p.1 - p.2 = z} = {z + t} := by
        ext s; simp only [mem_preimage, mem_ofPred_eq, mem_singleton_iff]
        constructor <;> intro h <;> linarith
      rw [e, uLaw_of_lt h, unifI_apply (measurableSet_singleton _),
        measure_mono_null inter_subset_left (measure_singleton _), mul_zero]
    simp_rw [h0]; exact lintegral_zero
  · rw [Measure.prod_apply hm]
    have h0 : ∀ s, uLaw c d (Prod.mk s ⁻¹' {p : ℝ × ℝ | p.1 - p.2 = z}) = 0 := by
      intro s
      have e : Prod.mk s ⁻¹' {p : ℝ × ℝ | p.1 - p.2 = z} = {s - z} := by
        ext t; simp only [mem_preimage, mem_ofPred_eq, mem_singleton_iff]
        constructor <;> intro h <;> linarith
      rw [e, uLaw_of_lt h, unifI_apply (measurableSet_singleton _),
        measure_mono_null inter_subset_left (measure_singleton _), mul_zero]
    simp_rw [h0]; exact lintegral_zero

/-! ## Piecewise form and bounds of `cdfR` -/

lemma ramp_of_nonpos {t : ℝ} (h : t ≤ 0) : ramp t = 0 := max_eq_right h
lemma ramp_of_nonneg {t : ℝ} (h : 0 ≤ t) : ramp t = t := max_eq_left h

/-- the ramp formula for two proper intervals with widths `p ≤ q` -/
lemma ramp_formula_le {U p q : ℝ} (hp : 0 < p) (hpq : p ≤ q) :
    (ramp U ^ 2 - ramp (U - p) ^ 2 - ramp (U - q) ^ 2 + ramp (U - p - q) ^ 2) / (2 * p * q) =
      if U ≤ 0 then 0
      else if U ≤ p then U ^ 2 / (2 * p * q)
      else if U ≤ q then (2 * U - p) / (2 * q)
      else if U ≤ p + q then 1 - (p + q - U) ^ 2 / (2 * p * q)
      else 1 := by
  have hq : 0 < q := hp.trans_le hpq
  split_ifs with c1 c2 c3 c4
  · rw [ramp_of_nonpos c1, ramp_of_nonpos (by linarith), ramp_of_nonpos (by linarith),
      ramp_of_nonpos (by linarith)]; simp
  · rw [ramp_of_nonneg (by linarith), ramp_of_nonpos (by linarith), ramp_of_nonpos (by linarith),
      ramp_of_nonpos (by linarith)]; ring
  · rw [ramp_of_nonneg (by linarith), ramp_of_nonneg (by linarith), ramp_of_nonpos (by linarith),
      ramp_of_nonpos (by linarith)]
    field_simp; ring
  · rw [ramp_of_nonneg (by linarith), ramp_of_nonneg (by linarith), ramp_of_nonneg (by linarith),
      ramp_of_nonpos (by linarith)]
    field_simp; ring
  · rw [ramp_of_nonneg (by linarith), ramp_of_nonneg (by linarith), ramp_of_nonneg (by linarith),
      ramp_of_nonneg (by linarith)]
    field_simp; ring

/-- `cdfR` for two proper intervals, piecewise (`P = min`, `Q = max` of the widths, `U = z + d - a`) -/
lemma cdfR_piece {a b c d : ℝ} (hab : a < b) (hcd : c < d) (z : ℝ) :
    cdfR a b c d z =
      if z + d - a ≤ 0 then 0
      else if z + d - a ≤ min (b - a) (d - c) then
        (z + d - a) ^ 2 / (2 * min (b - a) (d - c) * max (b - a) (d - c))
      else if z + d - a ≤ max (b - a) (d - c) then
        (2 * (z + d - a) - min (b - a) (d - c)) / (2 * max (b - a) (d - c))
      else if z + d - a ≤ min (b - a) (d - c) + max (b - a) (d - c) then
        1 - (min (b - a) (d - c) + max (b - a) (d - c) - (z + d - a)) ^ 2 /
          (2 * min (b - a) (d - c) * max (b - a) (d - c))
      else 1 := by
  have hw1 : 0 < b - a := sub_pos.2 hab
  have hw2 : 0 < d - c := sub_pos.2 hcd
  simp only [cdfR, hab.ne, hcd.ne, and_false, ↓reduceIte]
  rcases le_total (b - a) (d - c) with h | h
  · rw [min_eq_left h, max_eq_right h, ← ramp_formula_le hw1 h]
    congr 1
    · rw [show z + d - b = z + d - a - (b - a) by ring, show z + c - a = z + d - a - (d - c) by ring,
        show z + c - b = z + d - a - (b - a) - (d - c) by ring]
  · rw [min_eq_right h, max_eq_left h, ← ramp_formula_le hw2 h]
    rw [show z + d - b = z + d - a - (b - a) by ring, show z + c - a = z + d - a - (d - c) by ring,
      show z + c - b = z + d - a - (b - a) - (d - c) by ring,
      show z + d - a - (b - a) - (d - c) = z + d - a - (d - c) - (b - a) by ring]
    ring

lemma cdfR_mem01 {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d) (z : ℝ) :
    0 ≤ cdfR a b c d z ∧ cdfR a b c d z ≤ 1 := by
  rcases eq_or_lt_of_le hab with hab' | hab' <;> rcases eq_or_lt_of_le hcd with hcd' | hcd'
  · subst hab' hcd'; simp only [cdfR, and_self, ↓reduceIte]; split_ifs <;> norm_num
  · subst hab'; simp only [cdfR, hcd'.ne, and_false, ↓reduceIte]
    exact ⟨le_min (le_max_right _ _) zero_le_one, min_le_right _ _⟩
  · subst hcd'; simp only [cdfR, hab'.ne, and_true, ↓reduceIte]
    exact ⟨le_min (le_max_right _ _) zero_le_one, min_le_right _ _⟩
  · rw [cdfR_piece hab' hcd']
    have hw1 : 0 < b - a := sub_pos.2 hab'
    have hw2 : 0 < d - c := sub_pos.2 hcd'
    set P := min (b - a) (d - c)
    set Q := max (b - a) (d - c)
    set U := z + d - a
    have hP : 0 < P := lt_min hw1 hw2
    have hPQ : P ≤ Q := min_le_max
    have hQ : 0 < Q := hP.trans_le hPQ
    split_ifs with c1 c2 c3 c4
    · norm_num
    · constructor
      · positivity
      · rw [div_le_one (by positivity)]; nlinarith
    · constructor
      · exact div_nonneg (by linarith) (by positivity)
      · rw [div_le_one (by positivity)]; linarith
    · have hpos : 0 < 2 * P * Q := by positivity
      constructor
      · rw [sub_nonneg, div_le_one hpos]; nlinarith
      · have : 0 ≤ (P + Q - U) ^ 2 / (2 * P * Q) := by positivity
        linarith
    · norm_num

end BHH
