/-
T6 helpers: the pointwise bound of `(|δ_i| + |δ_j|) T_ij(|δ_j - δ_i|)` by a function of
`X = |δ_i| + |δ_j|` alone, its integrated form (`pairRem` from `E X ≤ S1`, `E X² ≤ S2`), the second moment and mean
distance about a point (from the moment about the centroid), and the gradient term (`|∇| ≤ 2`).
-/
import W2.TabProps
import W2.GeoGrad

open MeasureTheory Set Real
open scoped ENNReal

noncomputable section

namespace BHH.W2

open BHH

/-! ## The Euclidean norm -/

lemma tp_enorm2_eq_norm (u : Pt) : enorm2 u = ‖(⟨u.1, u.2⟩ : ℂ)‖ := by
  rw [Complex.norm_eq_sqrt_sq_add_sq]; rfl

lemma tp_enorm2_nonneg (u : Pt) : 0 ≤ enorm2 u := Real.sqrt_nonneg _

lemma tp_enorm2_sub_le (u v : Pt) : enorm2 (u - v) ≤ enorm2 u + enorm2 v := by
  rw [tp_enorm2_eq_norm, tp_enorm2_eq_norm, tp_enorm2_eq_norm]
  have : (⟨(u - v).1, (u - v).2⟩ : ℂ) = (⟨u.1, u.2⟩ : ℂ) - ⟨v.1, v.2⟩ := by
    apply Complex.ext <;> simp
  rw [this]
  exact norm_sub_le _ _

lemma tp_enorm2_sq (u : Pt) : enorm2 u ^ 2 = u.1 ^ 2 + u.2 ^ 2 := Real.sq_sqrt (by positivity)

lemma tp_continuous_enorm2 : Continuous enorm2 := by unfold enorm2; fun_prop

/-- Cauchy–Schwarz in the plane -/
lemma tp_inner_le_enorm2 (g u : Pt) : g.1 * u.1 + g.2 * u.2 ≤ enorm2 g * enorm2 u := by
  have h1 := tp_enorm2_sq g
  have h2 := tp_enorm2_sq u
  have hg := tp_enorm2_nonneg g
  have hu := tp_enorm2_nonneg u
  nlinarith [sq_nonneg (g.1 * u.2 - g.2 * u.1), sq_nonneg (enorm2 g * enorm2 u - (g.1 * u.1 + g.2 * u.2)),
    mul_nonneg hg hu]

/-! ## The pointwise bound -/

/-- the bound of `X T(D)` for `D ≤ X` (`μ = 2 arcsin(min(d⁺,2)/2) - 2 arcsin(d⁻/2)`) -/
def Qf (dlo dhi : ℝ) (first : Bool) (X : ℝ) : ℝ :=
  (if first then X ^ 2 / √(4 - dhi ^ 2) else (2 * Real.arcsin (min dhi 2 / 2) - 2 * Real.arcsin (dlo / 2)) * X) +
    min (X ^ 2 / dlo) (π * X)

lemma mul_Tseg_le_Qf {dlo dhi : ℝ} {first : Bool} {X D : ℝ} (hdlo : 0 < dlo) (hfirst : first = true → dhi < 2)
    (hX : 0 ≤ X) (hD0 : 0 ≤ D) (hDX : D ≤ X) : X * Tseg dlo dhi first D ≤ Qf dlo dhi first X := by
  unfold Tseg Qf
  rw [mul_add]
  refine add_le_add ?_ ?_
  · cases first with
    | true =>
      simp only [↓reduceIte]
      calc X * (D / √(4 - dhi ^ 2)) ≤ X * (X / √(4 - dhi ^ 2)) :=
            mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hDX (Real.sqrt_nonneg _)) hX
        _ = X ^ 2 / √(4 - dhi ^ 2) := by ring
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [mul_comm]
  · refine le_min ?_ ?_
    · calc X * min (D / dlo) π ≤ X * (D / dlo) := mul_le_mul_of_nonneg_left (min_le_left _ _) hX
        _ ≤ X * (X / dlo) := mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hDX hdlo.le) hX
        _ = X ^ 2 / dlo := by ring
    · calc X * min (D / dlo) π ≤ X * π := mul_le_mul_of_nonneg_left (min_le_right _ _) hX
        _ = π * X := mul_comm _ _

lemma continuous_Qf (dlo dhi : ℝ) (first : Bool) : Continuous (Qf dlo dhi first) := by
  unfold Qf
  cases first <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> fun_prop

/-! ## Integrals over bounded sets -/

lemma tp_integrableOn_of_bounded {α : Type*} [MeasurableSpace α] [MetricSpace α] [ProperSpace α]
    [OpensMeasurableSpace α] {μ : Measure α} [IsFiniteMeasureOnCompacts μ] {S : Set α}
    (hS : Bornology.IsBounded S) {f : α → ℝ} (hf : Continuous f) : IntegrableOn f S μ :=
  (ContinuousOn.integrableOn_compact hS.isCompact_closure hf.continuousOn).mono_set subset_closure

/-- the integrated bound: `∫ Qf(X) ≤ pairRem(S1, S2) m` from `∫ X ≤ S1 m`, `∫ X² ≤ S2 m` -/
lemma integral_Qf_le {α : Type*} [MeasurableSpace α] {μ : Measure α} {S : Set α} {X : α → ℝ}
    {dlo dhi : ℝ} {first : Bool} {S1 S2 m : ℝ}
    (hXi : IntegrableOn X S μ) (hX2i : IntegrableOn (fun p => X p ^ 2) S μ) (hm : 0 ≤ m)
    (h1 : ∫ p in S, X p ∂μ ≤ S1 * m) (h2 : ∫ p in S, X p ^ 2 ∂μ ≤ S2 * m) (hdlo : 0 < dlo)
    (hμ : first = false → 0 ≤ 2 * Real.arcsin (min dhi 2 / 2) - 2 * Real.arcsin (dlo / 2)) :
    ∫ p in S, Qf dlo dhi first (X p) ∂μ ≤ pairRem dlo dhi first S1 S2 * m := by
  set μ' := 2 * Real.arcsin (min dhi 2 / 2) - 2 * Real.arcsin (dlo / 2) with hμ'
  have iA : IntegrableOn (fun p => X p ^ 2 / dlo) S μ := hX2i.div_const dlo
  have iB : IntegrableOn (fun p => π * X p) S μ := hXi.const_mul π
  have iM : IntegrableOn (fun p => min (X p ^ 2 / dlo) (π * X p)) S μ := Integrable.inf iA iB
  have hmin : ∫ p in S, min (X p ^ 2 / dlo) (π * X p) ∂μ ≤ min (S2 / dlo) (π * S1) * m := by
    rw [min_mul_of_nonneg _ _ hm]
    refine le_min ?_ ?_
    · calc ∫ p in S, min (X p ^ 2 / dlo) (π * X p) ∂μ ≤ ∫ p in S, X p ^ 2 / dlo ∂μ :=
            integral_mono iM iA fun p => min_le_left _ _
        _ = (∫ p in S, X p ^ 2 ∂μ) / dlo := integral_div dlo _
        _ ≤ (S2 * m) / dlo := div_le_div_of_nonneg_right h2 hdlo.le
        _ = S2 / dlo * m := by ring
    · calc ∫ p in S, min (X p ^ 2 / dlo) (π * X p) ∂μ ≤ ∫ p in S, π * X p ∂μ :=
            integral_mono iM iB fun p => min_le_right _ _
        _ = π * ∫ p in S, X p ∂μ := integral_const_mul π _
        _ ≤ π * (S1 * m) := mul_le_mul_of_nonneg_left h1 Real.pi_pos.le
        _ = π * S1 * m := by ring
  unfold Qf pairRem
  cases first with
  | true =>
    simp only [↓reduceIte]
    have iF : IntegrableOn (fun p => X p ^ 2 / √(4 - dhi ^ 2)) S μ := hX2i.div_const _
    rw [integral_add iF iM, add_mul]
    refine add_le_add ?_ hmin
    calc ∫ p in S, X p ^ 2 / √(4 - dhi ^ 2) ∂μ = (∫ p in S, X p ^ 2 ∂μ) / √(4 - dhi ^ 2) := integral_div _ _
      _ ≤ (S2 * m) / √(4 - dhi ^ 2) := div_le_div_of_nonneg_right h2 (Real.sqrt_nonneg _)
      _ = S2 / √(4 - dhi ^ 2) * m := by ring
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    have iF : IntegrableOn (fun p => μ' * X p) S μ := hXi.const_mul μ'
    rw [integral_add iF iM, add_mul]
    refine add_le_add ?_ hmin
    calc ∫ p in S, μ' * X p ∂μ = μ' * ∫ p in S, X p ∂μ := integral_const_mul μ' _
      _ ≤ μ' * (S1 * m) := mul_le_mul_of_nonneg_left h1 (hμ rfl)
      _ = μ' * S1 * m := by ring

/-! ## Moments about a point -/

lemma tp_cen_fst_mul {W : Set Pt} (hW0 : volume W ≠ 0) (hWt : volume W ≠ ⊤) :
    (volume W).toReal * (cen W).1 = ∫ w in W, w.1 := by
  have hV : (volume W).toReal ≠ 0 := (ENNReal.toReal_pos hW0 hWt).ne'
  simp only [cen]; field_simp

lemma tp_cen_snd_mul {W : Set Pt} (hW0 : volume W ≠ 0) (hWt : volume W ≠ ⊤) :
    (volume W).toReal * (cen W).2 = ∫ w in W, w.2 := by
  have hV : (volume W).toReal ≠ 0 := (ENNReal.toReal_pos hW0 hWt).ne'
  simp only [cen]; field_simp

/-- second moment and mean distance about a point `q`, from the moment about the centroid -/
lemma tp_moment_bound {W : Set Pt} (hW0 : volume W ≠ 0) (hWt : volume W ≠ ⊤) (hWb : Bornology.IsBounded W)
    (q : Pt) {M e : ℝ} (hM : (volume W).toReal⁻¹ * ∫ w in W, sqDist w (cen W) ≤ M) (he : edist2 (cen W) q ≤ e) :
    ∫ w in W, sqDist w q ≤ (volume W).toReal * (M + e ^ 2) ∧
      ∫ w in W, edist2 w q ≤ (volume W).toReal * √(M + e ^ 2) := by
  set V := (volume W).toReal with hVdef
  have hV : 0 < V := ENNReal.toReal_pos hW0 hWt
  set C := cen W with hC
  have i1 : IntegrableOn (fun w : Pt => w.1) W := tp_integrableOn_of_bounded hWb continuous_fst
  have i2 : IntegrableOn (fun w : Pt => w.2) W := tp_integrableOn_of_bounded hWb continuous_snd
  have iC : IntegrableOn (fun w : Pt => sqDist w C) W := tp_integrableOn_of_bounded hWb (by unfold sqDist; fun_prop)
  have iq : IntegrableOn (fun w : Pt => sqDist w q) W := tp_integrableOn_of_bounded hWb (by unfold sqDist; fun_prop)
  have hc1 : V * C.1 = ∫ w in W, w.1 := tp_cen_fst_mul hW0 hWt
  have hc2 : V * C.2 = ∫ w in W, w.2 := tp_cen_snd_mul hW0 hWt
  -- `sqDist w q = sqDist w C + 2 ⟨C - q, w⟩ - 2 ⟨C - q, C⟩ + sqDist C q`
  obtain ⟨K, hK⟩ : ∃ K, K = sqDist C q - 2 * (C.1 - q.1) * C.1 - 2 * (C.2 - q.2) * C.2 := ⟨_, rfl⟩
  have hid : ∀ w : Pt, sqDist w q = sqDist w C + (2 * (C.1 - q.1) * w.1 + 2 * (C.2 - q.2) * w.2) + K := by
    intro w; rw [hK]; unfold sqDist; ring
  have hint : ∫ w in W, sqDist w q = (∫ w in W, sqDist w C) + V * sqDist C q := by
    have h1 : ∫ w in W, sqDist w q =
        ∫ w in W, (sqDist w C + (2 * (C.1 - q.1) * w.1 + 2 * (C.2 - q.2) * w.2) + K) :=
      integral_congr_ae (Filter.Eventually.of_forall hid)
    have iL : IntegrableOn (fun w : Pt => 2 * (C.1 - q.1) * w.1 + 2 * (C.2 - q.2) * w.2) W :=
      (i1.const_mul _).add (i2.const_mul _)
    have iCL : IntegrableOn (fun w : Pt => sqDist w C + (2 * (C.1 - q.1) * w.1 + 2 * (C.2 - q.2) * w.2)) W :=
      iC.add iL
    rw [h1, integral_add iCL (integrableOn_const (by exact hWt)), integral_add iC iL,
      integral_add (i1.const_mul _) (i2.const_mul _), integral_const_mul, integral_const_mul, setIntegral_const,
      measureReal_def, smul_eq_mul, ← hc1, ← hc2, ← hVdef, hK]
    ring
  have hsq : sqDist C q ≤ e ^ 2 := by
    have h0 : 0 ≤ edist2 C q := Real.sqrt_nonneg _
    have : edist2 C q ^ 2 = sqDist C q := Real.sq_sqrt (by unfold sqDist; positivity)
    nlinarith
  have hMV : ∫ w in W, sqDist w C ≤ V * M := by
    rw [inv_mul_le_iff₀ hV] at hM; exact hM
  have hfirst : ∫ w in W, sqDist w q ≤ V * (M + e ^ 2) := by
    rw [hint]; nlinarith
  refine ⟨hfirst, ?_⟩
  -- Cauchy–Schwarz: `(∫ f)² ≤ V ∫ f²`
  set f : Pt → ℝ := fun w => edist2 w q with hf
  have hf2 : ∀ w, f w ^ 2 = sqDist w q := fun w => Real.sq_sqrt (by unfold sqDist; positivity)
  have iF : IntegrableOn f W := tp_integrableOn_of_bounded hWb (by simp only [hf, edist2]; unfold sqDist; fun_prop)
  have hF0 : 0 ≤ ∫ w in W, f w := setIntegral_nonneg_of_ae_restrict (Filter.Eventually.of_forall fun w => Real.sqrt_nonneg _)
    |>.trans_eq rfl
  set t := (∫ w in W, f w) / V with ht
  have hvar : 0 ≤ ∫ w in W, (f w - t) ^ 2 := setIntegral_nonneg_of_ae_restrict
    (Filter.Eventually.of_forall fun w => sq_nonneg _)
  have e2 : ∀ w, (f w - t) ^ 2 = sqDist w q - 2 * t * f w + t ^ 2 := by intro w; rw [← hf2]; ring
  simp_rw [e2] at hvar
  have iqF : IntegrableOn (fun w : Pt => sqDist w q - 2 * t * f w) W := iq.sub (iF.const_mul _)
  rw [integral_add iqF (integrableOn_const (by exact hWt)), integral_sub iq (iF.const_mul _),
    integral_const_mul, setIntegral_const, measureReal_def, smul_eq_mul, ← hVdef] at hvar
  have hCS : (∫ w in W, f w) ^ 2 ≤ V * ∫ w in W, sqDist w q := by
    have : t * V = ∫ w in W, f w := by rw [ht]; field_simp
    nlinarith
  have h3 := mul_le_mul_of_nonneg_left hfirst hV.le
  have hb : (∫ w in W, f w) ^ 2 ≤ (V * √(M + e ^ 2)) ^ 2 := by
    have hMe : 0 ≤ M + e ^ 2 := by
      by_contra h
      have h' : M + e ^ 2 < 0 := lt_of_not_ge h
      have h4 : V * (V * (M + e ^ 2)) < 0 := mul_neg_of_pos_of_neg hV (mul_neg_of_pos_of_neg hV h')
      nlinarith [sq_nonneg (∫ w in W, f w)]
    rw [mul_pow, Real.sq_sqrt hMe]
    nlinarith
  exact (pow_le_pow_iff_left₀ hF0 (by positivity) two_ne_zero).1 hb

end BHH.W2
