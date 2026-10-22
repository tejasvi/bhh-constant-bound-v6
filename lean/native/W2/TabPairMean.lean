/-
T6: `PairMean`, the vertex lemma along segments integrated over a product of two cells.
For `(w, z) ∈ Z × Z'` the vertex lemma gives `A(-w, 0, z) ≤ A(c) + Σ_i ⟨∇_i A(c), δ_i⟩ + ϱ`; the gradient term
integrates to at most `2 (e0 + e2)` (`|∇| ≤ 2`, `E δ_0 = -(cen Z + c_0)`, `δ_1 = 0`, `E δ_2 = cen Z' - c_2`), and each
remainder term `ν (|δ_i| + |δ_j|) T(|δ_j - δ_i|) ≤ ν Qf(|δ_i| + |δ_j|)` integrates to at most `ν pairRem` by the moment
bounds (`E|δ_0|² ≤ M0 + e0²`, Jensen, independence of `w` and `z`).
-/
import W2.TabPairAux

open MeasureTheory Set Real
open scoped ENNReal

noncomputable section

namespace BHH.W2

open BHH

/-! ## Integrals over a product of two sets -/

section prod

variable {Z Z' : Set Pt}

lemma tp_vol_prod_toReal (Z Z' : Set Pt) :
    (volume (Z ×ˢ Z')).toReal = (volume Z).toReal * (volume Z').toReal := by
  rw [Measure.volume_eq_prod (α := Pt) (β := Pt), Measure.prod_prod, ENNReal.toReal_mul]

lemma tp_setIntegral_prod_fst' (f : Pt → ℝ) :
    ∫ p in Z ×ˢ Z', f p.1 = (∫ w in Z, f w) * (volume Z').toReal := by
  have h := setIntegral_prod_mul (μ := (volume : Measure Pt)) (ν := (volume : Measure Pt)) f (fun _ => (1 : ℝ)) Z Z'
  simp only [mul_one] at h
  rw [Measure.volume_eq_prod (α := Pt) (β := Pt), h, setIntegral_const, measureReal_def, smul_eq_mul, mul_one]

lemma tp_setIntegral_prod_snd' (h : Pt → ℝ) :
    ∫ p in Z ×ˢ Z', h p.2 = (volume Z).toReal * ∫ z in Z', h z := by
  have h' := setIntegral_prod_mul (μ := (volume : Measure Pt)) (ν := (volume : Measure Pt)) (fun _ => (1 : ℝ)) h Z Z'
  simp only [one_mul] at h'
  rw [Measure.volume_eq_prod (α := Pt) (β := Pt), h', setIntegral_const, measureReal_def, smul_eq_mul, mul_one]

lemma tp_setIntegral_prod_mul' (f h : Pt → ℝ) :
    ∫ p in Z ×ˢ Z', f p.1 * h p.2 = (∫ w in Z, f w) * ∫ z in Z', h z := by
  rw [Measure.volume_eq_prod (α := Pt) (β := Pt)]
  exact setIntegral_prod_mul f h Z Z'

end prod

lemma tp_enorm2_neg_sub (w c : Pt) : enorm2 (-w - c) = edist2 w (-c) := by
  unfold enorm2 edist2 sqDist
  congr 1
  simp only [Prod.fst_sub, Prod.snd_sub, Prod.fst_neg, Prod.snd_neg]
  ring

lemma tp_enorm2_sub_eq (z c : Pt) : enorm2 (z - c) = edist2 z c := rfl

lemma tp_edist2_sq (w q : Pt) : edist2 w q ^ 2 = sqDist w q := Real.sq_sqrt (by unfold sqDist; positivity)

lemma tp_edist2_nonneg (w q : Pt) : 0 ≤ edist2 w q := Real.sqrt_nonneg _

lemma tp_continuous_edist2_left (q : Pt) : Continuous fun w => edist2 w q := by
  unfold edist2 sqDist; fun_prop


/-! ## The pointwise bound -/

/-- the gradient term `⟨∇_{y_i} A(c), δ⟩` -/
def gradTerm (c : Fin 3 → Pt) (i : Fin 3) (δ : Pt) : ℝ := (greenGrad c i).1 * δ.1 + (greenGrad c i).2 * δ.2

/-- the bound of the remainder term of the pair `(i, j)` as a function of `X = |δ_i| + |δ_j|` -/
def remTerm (c : Fin 3 → Pt) (eps : Fin 3 → ℝ) (dlo dhi : Fin 3 → Fin 3 → ℝ) (first : Fin 3 → Fin 3 → Bool)
    (i j : Fin 3) (X : ℝ) : ℝ :=
  if dlo i j < 2 then (nuCountSeg c eps dlo dhi first i j : ℝ) * Qf (dlo i j) (dhi i j) (first i j) X else 0

lemma ite_rem_le {P : Prop} {i1 i2 : Decidable P} {ν : ℝ} (hν : 0 ≤ ν) {dlo dhi : ℝ}
    {first : Bool} (hdlo : 0 < dlo) (hfirst : first = true → dhi < 2) {a b D : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hD : 0 ≤ D) (hDab : D ≤ a + b) :
    @ite _ P i1 (ν * (a + b) * Tseg dlo dhi first D) 0 ≤ @ite _ P i2 (ν * Qf dlo dhi first (a + b)) 0 := by
  by_cases h : P
  · simp only [h, ↓reduceIte]
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (mul_Tseg_le_Qf hdlo hfirst (add_nonneg ha hb) hD hDab) hν
  · simp only [h, ↓reduceIte, le_refl]

lemma pairMean_pt (hV : VertexLemmaSeg) {c : Fin 3 → Pt} {eps : Fin 3 → ℝ} {dlo dhi : Fin 3 → Fin 3 → ℝ}
    {first : Fin 3 → Fin 3 → Bool} {U0 : ℝ} (hc1 : c 1 = 0) (hdlo : ∀ i j, i < j → 0 < dlo i j)
    (hfirst : ∀ i j, i < j → first i j = true → dhi i j < 2) {w z : Pt}
    (hseg : ∀ i j, i < j → ∀ t ∈ Icc (0 : ℝ) 1,
        dlo i j ≤ edist2 (segPt (c i) (![-w, (0 : Pt), z] i) t) (segPt (c j) (![-w, (0 : Pt), z] j) t) ∧
        edist2 (segPt (c i) (![-w, (0 : Pt), z] i) t) (segPt (c j) (![-w, (0 : Pt), z] j) t) ≤ dhi i j)
    (heps : ∀ i, enorm2 (![-w, (0 : Pt), z] i - c i) ≤ eps i) (hU : unionArea c ≤ U0) :
    unionArea ![-w, (0 : Pt), z] ≤ U0 + gradTerm c 0 (-w - c 0) + gradTerm c 2 (z - c 2) +
      remTerm c eps dlo dhi first 0 1 (edist2 w (-c 0)) +
      remTerm c eps dlo dhi first 0 2 (edist2 w (-c 0) + edist2 z (c 2)) +
      remTerm c eps dlo dhi first 1 2 (edist2 z (c 2)) := by
  have h := hV 3 c ![-w, (0 : Pt), z] eps dlo dhi first hdlo hseg hfirst heps
  have h2 := (abs_le.1 h).2
  have hG : ∑ i : Fin 3, ((greenGrad c i).1 * (![-w, (0 : Pt), z] i - c i).1 +
      (greenGrad c i).2 * (![-w, (0 : Pt), z] i - c i).2) = gradTerm c 0 (-w - c 0) + gradTerm c 2 (z - c 2) := by
    rw [Fin.sum_univ_three]
    simp [gradTerm, hc1]
  have hν : ∀ i j, 0 ≤ (nuCountSeg c eps dlo dhi first i j : ℝ) := fun i j => Nat.cast_nonneg _
  have e0 : enorm2 (0 - c 1) = 0 := by rw [hc1, sub_zero]; simp [enorm2]
  have hR : vertexRemSeg c ![-w, (0 : Pt), z] eps dlo dhi first ≤
      remTerm c eps dlo dhi first 0 1 (edist2 w (-c 0)) +
      remTerm c eps dlo dhi first 0 2 (edist2 w (-c 0) + edist2 z (c 2)) +
      remTerm c eps dlo dhi first 1 2 (edist2 z (c 2)) := by
    unfold vertexRemSeg remTerm
    simp only [Fin.sum_univ_three, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, lt_self_iff_false, false_and, ↓reduceIte, add_zero, zero_add]
    have l01 : (0 : Fin 3) < 1 := by decide
    have l02 : (0 : Fin 3) < 2 := by decide
    have l12 : (1 : Fin 3) < 2 := by decide
    have n10 : ¬ (1 : Fin 3) < 0 := by decide
    have n20 : ¬ (2 : Fin 3) < 0 := by decide
    have n21 : ¬ (2 : Fin 3) < 1 := by decide
    simp only [l01, l02, l12, n10, n20, n21, true_and, false_and, ↓reduceIte, add_zero, zero_add]
    rw [← tp_enorm2_neg_sub, ← tp_enorm2_sub_eq]
    refine add_le_add (add_le_add ?_ ?_) ?_
    · rw [show ∀ X : ℝ, Qf (dlo 0 1) (dhi 0 1) (first 0 1) X =
          Qf (dlo 0 1) (dhi 0 1) (first 0 1) (X + enorm2 (0 - c 1)) from fun X => by rw [e0, add_zero]]
      exact ite_rem_le (hν 0 1) (hdlo 0 1 l01) (hfirst 0 1 l01) (tp_enorm2_nonneg _) (tp_enorm2_nonneg _)
        (tp_enorm2_nonneg _) (by rw [add_comm]; exact tp_enorm2_sub_le _ _)
    · exact ite_rem_le (hν 0 2) (hdlo 0 2 l02) (hfirst 0 2 l02) (tp_enorm2_nonneg _) (tp_enorm2_nonneg _)
        (tp_enorm2_nonneg _) (by rw [add_comm]; exact tp_enorm2_sub_le _ _)
    · rw [show ∀ X : ℝ, Qf (dlo 1 2) (dhi 1 2) (first 1 2) X =
          Qf (dlo 1 2) (dhi 1 2) (first 1 2) (enorm2 (0 - c 1) + X) from fun X => by rw [e0, zero_add]]
      exact ite_rem_le (hν 1 2) (hdlo 1 2 l12) (hfirst 1 2 l12) (tp_enorm2_nonneg _) (tp_enorm2_nonneg _)
        (tp_enorm2_nonneg _) (by rw [add_comm]; exact tp_enorm2_sub_le _ _)
  rw [hG] at h2
  linarith


/-! ## Integrated pieces -/

lemma continuous_remTerm (c : Fin 3 → Pt) (eps : Fin 3 → ℝ) (dlo dhi : Fin 3 → Fin 3 → ℝ)
    (first : Fin 3 → Fin 3 → Bool) (i j : Fin 3) : Continuous (remTerm c eps dlo dhi first i j) := by
  unfold remTerm
  split_ifs
  · exact continuous_const.mul (continuous_Qf _ _ _)
  · exact continuous_const

lemma gradTerm_le (c : Fin 3 → Pt) (i : Fin 3) (δ : Pt) : gradTerm c i δ ≤ 2 * enorm2 δ := by
  have hg : enorm2 (greenGrad c i) ≤ 2 := by
    have h4 := greenGradLe 3 c i
    unfold enorm2
    rw [show (2 : ℝ) = √4 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt h4
  calc gradTerm c i δ ≤ enorm2 (greenGrad c i) * enorm2 δ := tp_inner_le_enorm2 _ _
    _ ≤ 2 * enorm2 δ := mul_le_mul_of_nonneg_right hg (tp_enorm2_nonneg _)

/-- integral of an affine function over a set: `∫_W (a w.1 + b w.2 + k) = V (a C.1 + b C.2 + k)` -/
lemma tp_integral_affine {W : Set Pt} (hW0 : volume W ≠ 0) (hWt : volume W ≠ ⊤) (hWb : Bornology.IsBounded W)
    (a b k : ℝ) :
    ∫ w in W, (a * w.1 + b * w.2 + k) = (volume W).toReal * (a * (cen W).1 + b * (cen W).2 + k) := by
  have i1 : IntegrableOn (fun w : Pt => a * w.1) W :=
    (tp_integrableOn_of_bounded hWb continuous_fst).const_mul a
  have i2 : IntegrableOn (fun w : Pt => b * w.2) W :=
    (tp_integrableOn_of_bounded hWb continuous_snd).const_mul b
  have i12 : IntegrableOn (fun w : Pt => a * w.1 + b * w.2) W := i1.add i2
  have hc1 := tp_cen_fst_mul hW0 hWt
  have hc2 := tp_cen_snd_mul hW0 hWt
  rw [integral_add i12 (integrableOn_const (by exact hWt)), integral_add i1 i2, integral_const_mul,
    integral_const_mul, setIntegral_const, measureReal_def, smul_eq_mul, ← hc1, ← hc2]
  ring

lemma integral_gradTerm_neg {W : Set Pt} (hW0 : volume W ≠ 0) (hWt : volume W ≠ ⊤) (hWb : Bornology.IsBounded W)
    (c : Fin 3 → Pt) (i : Fin 3) (q : Pt) :
    ∫ w in W, gradTerm c i (-w - q) = (volume W).toReal * gradTerm c i (-(cen W) - q) := by
  have e : ∀ w : Pt, gradTerm c i (-w - q) = -(greenGrad c i).1 * w.1 + -(greenGrad c i).2 * w.2 +
      -((greenGrad c i).1 * q.1 + (greenGrad c i).2 * q.2) := by
    intro w; unfold gradTerm; simp only [Prod.fst_sub, Prod.snd_sub, Prod.fst_neg, Prod.snd_neg]; ring
  rw [integral_congr_ae (Filter.Eventually.of_forall e), tp_integral_affine hW0 hWt hWb, e]

lemma integral_gradTerm_sub {W : Set Pt} (hW0 : volume W ≠ 0) (hWt : volume W ≠ ⊤) (hWb : Bornology.IsBounded W)
    (c : Fin 3 → Pt) (i : Fin 3) (q : Pt) :
    ∫ w in W, gradTerm c i (w - q) = (volume W).toReal * gradTerm c i (cen W - q) := by
  have e : ∀ w : Pt, gradTerm c i (w - q) = (greenGrad c i).1 * w.1 + (greenGrad c i).2 * w.2 +
      -((greenGrad c i).1 * q.1 + (greenGrad c i).2 * q.2) := by
    intro w; unfold gradTerm; simp only [Prod.fst_sub, Prod.snd_sub]; ring
  rw [integral_congr_ae (Filter.Eventually.of_forall e), tp_integral_affine hW0 hWt hWb, e]

lemma integral_remTerm_le {c : Fin 3 → Pt} {eps : Fin 3 → ℝ} {dlo dhi : Fin 3 → Fin 3 → ℝ}
    {first : Fin 3 → Fin 3 → Bool} {S : Set (Pt × Pt)} {X : Pt × Pt → ℝ} (i j : Fin 3) {S1 S2 m : ℝ}
    (hm : 0 ≤ m) (hXi : IntegrableOn X S) (hX2i : IntegrableOn (fun p => X p ^ 2) S)
    (h1 : ∫ p in S, X p ≤ S1 * m) (h2 : ∫ p in S, X p ^ 2 ≤ S2 * m) (hdlo : 0 < dlo i j)
    (hμ : dlo i j < 2 → first i j = false →
      0 ≤ 2 * Real.arcsin (min (dhi i j) 2 / 2) - 2 * Real.arcsin (dlo i j / 2)) :
    ∫ p in S, remTerm c eps dlo dhi first i j (X p) ≤
      (if dlo i j < 2 then (nuCountSeg c eps dlo dhi first i j : ℝ) *
        pairRem (dlo i j) (dhi i j) (first i j) S1 S2 else 0) * m := by
  unfold remTerm
  by_cases h : dlo i j < 2
  · simp only [h, ↓reduceIte]
    rw [integral_const_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (integral_Qf_le hXi hX2i hm h1 h2 hdlo (hμ h)) (Nat.cast_nonneg _)
  · simp only [h, ↓reduceIte, integral_zero, zero_mul, le_refl]


/-! ## T6 -/

set_option maxHeartbeats 2000000 in
theorem pairMean : PairMean := by
  intro hV Z Z' c eps dlo dhi first U0 e0 e2 M0 M2 hZm hZ'm hZ0 hZt hZ'0 hZ't hZb hZ'b hc1 hdlo hfirst hseg heps hU
    he0 he2 hM0 hM2
  obtain ⟨V, hVdef⟩ : ∃ V, V = (volume Z).toReal := ⟨_, rfl⟩
  obtain ⟨V', hV'def⟩ : ∃ V', V' = (volume Z').toReal := ⟨_, rfl⟩
  have hVp : 0 < V := by rw [hVdef]; exact ENNReal.toReal_pos hZ0 hZt
  have hV'p : 0 < V' := by rw [hV'def]; exact ENNReal.toReal_pos hZ'0 hZ't
  rw [← hVdef, ← hV'def]
  have hSm : MeasurableSet (Z ×ˢ Z') := hZm.prod hZ'm
  have hSb : Bornology.IsBounded (Z ×ˢ Z') := hZb.prod hZ'b
  have hS : (volume (Z ×ˢ Z')).toReal = V * V' := by rw [tp_vol_prod_toReal, hVdef, hV'def]
  have hSt : volume (Z ×ˢ Z') ≠ ⊤ := by
    rw [Measure.volume_eq_prod (α := Pt) (β := Pt), Measure.prod_prod]; exact ENNReal.mul_ne_top hZt hZ't
  have hm : 0 ≤ V * V' := by positivity
  -- moments
  obtain ⟨hZsq, hZab⟩ := tp_moment_bound hZ0 hZt hZb (-c 0) hM0 he0
  obtain ⟨hZ'sq, hZ'ab⟩ := tp_moment_bound hZ'0 hZ't hZ'b (c 2) hM2 he2
  rw [← hVdef] at hZsq hZab
  rw [← hV'def] at hZ'sq hZ'ab
  set m0 := M0 + e0 ^ 2 with hm0
  set m2 := M2 + e2 ^ 2 with hm2
  have hA0 : 0 ≤ ∫ w in Z, edist2 w (-c 0) := setIntegral_nonneg hZm fun w _ => tp_edist2_nonneg _ _
  have hA2 : 0 ≤ ∫ z in Z', edist2 z (c 2) := setIntegral_nonneg hZ'm fun z _ => tp_edist2_nonneg _ _
  have hsq0 : ∫ w in Z, edist2 w (-c 0) ^ 2 = ∫ w in Z, sqDist w (-c 0) :=
    integral_congr_ae (Filter.Eventually.of_forall fun w => tp_edist2_sq w (-c 0))
  have hsq2 : ∫ z in Z', edist2 z (c 2) ^ 2 = ∫ z in Z', sqDist z (c 2) :=
    integral_congr_ae (Filter.Eventually.of_forall fun z => tp_edist2_sq z (c 2))
  -- `dlo ≤ dhi` (the product is nonempty), hence `μ ≥ 0` on the terms used
  obtain ⟨w₀, hw₀⟩ := nonempty_of_measure_ne_zero hZ0
  obtain ⟨z₀, hz₀⟩ := nonempty_of_measure_ne_zero hZ'0
  have hμ : ∀ i j, i < j → dlo i j < 2 → first i j = false →
      0 ≤ 2 * Real.arcsin (min (dhi i j) 2 / 2) - 2 * Real.arcsin (dlo i j / 2) := by
    intro i j hij hd _
    have h := hseg w₀ hw₀ z₀ hz₀ i j hij 0 ⟨le_rfl, zero_le_one⟩
    have hle : dlo i j ≤ min (dhi i j) 2 := le_min (h.1.trans h.2) hd.le
    have := Real.arcsin_le_arcsin (div_le_div_of_nonneg_right hle (by norm_num : (0 : ℝ) ≤ 2))
    linarith
  have l01 : (0 : Fin 3) < 1 := by decide
  have l02 : (0 : Fin 3) < 2 := by decide
  have l12 : (1 : Fin 3) < 2 := by decide
  -- the functions on the product and their integrability
  have cX0 : Continuous fun p : Pt × Pt => edist2 p.1 (-c 0) := (tp_continuous_edist2_left _).comp continuous_fst
  have cX2 : Continuous fun p : Pt × Pt => edist2 p.2 (c 2) := (tp_continuous_edist2_left _).comp continuous_snd
  have iX0 : IntegrableOn (fun p : Pt × Pt => edist2 p.1 (-c 0)) (Z ×ˢ Z') := tp_integrableOn_of_bounded hSb cX0
  have iX2 : IntegrableOn (fun p : Pt × Pt => edist2 p.2 (c 2)) (Z ×ˢ Z') := tp_integrableOn_of_bounded hSb cX2
  have iX02 : IntegrableOn (fun p : Pt × Pt => edist2 p.1 (-c 0) + edist2 p.2 (c 2)) (Z ×ˢ Z') := iX0.add iX2
  have iX0s : IntegrableOn (fun p : Pt × Pt => edist2 p.1 (-c 0) ^ 2) (Z ×ˢ Z') :=
    tp_integrableOn_of_bounded hSb (cX0.pow 2)
  have iX2s : IntegrableOn (fun p : Pt × Pt => edist2 p.2 (c 2) ^ 2) (Z ×ˢ Z') :=
    tp_integrableOn_of_bounded hSb (cX2.pow 2)
  have iX02s : IntegrableOn (fun p : Pt × Pt => (edist2 p.1 (-c 0) + edist2 p.2 (c 2)) ^ 2) (Z ×ˢ Z') :=
    tp_integrableOn_of_bounded hSb ((cX0.add cX2).pow 2)
  have cg0 : Continuous fun p : Pt × Pt => gradTerm c 0 (-p.1 - c 0) := by unfold gradTerm; fun_prop
  have cg2 : Continuous fun p : Pt × Pt => gradTerm c 2 (p.2 - c 2) := by unfold gradTerm; fun_prop
  have cR01 : Continuous fun p : Pt × Pt => remTerm c eps dlo dhi first 0 1 (edist2 p.1 (-c 0)) :=
    (continuous_remTerm _ _ _ _ _ 0 1).comp cX0
  have cR02 : Continuous fun p : Pt × Pt =>
      remTerm c eps dlo dhi first 0 2 (edist2 p.1 (-c 0) + edist2 p.2 (c 2)) :=
    (continuous_remTerm _ _ _ _ _ 0 2).comp (cX0.add cX2)
  have cR12 : Continuous fun p : Pt × Pt => remTerm c eps dlo dhi first 1 2 (edist2 p.2 (c 2)) :=
    (continuous_remTerm _ _ _ _ _ 1 2).comp cX2
  -- step 1: the integrand is bounded by `F`
  have hstep1 : ∫ p in Z ×ˢ Z', unionArea ![-p.1, (0 : Pt), p.2] ≤
      ∫ p in Z ×ˢ Z', (U0 + gradTerm c 0 (-p.1 - c 0) + gradTerm c 2 (p.2 - c 2) +
        remTerm c eps dlo dhi first 0 1 (edist2 p.1 (-c 0)) +
        remTerm c eps dlo dhi first 0 2 (edist2 p.1 (-c 0) + edist2 p.2 (c 2)) +
        remTerm c eps dlo dhi first 1 2 (edist2 p.2 (c 2))) := by
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun p => ENNReal.toReal_nonneg)
      (tp_integrableOn_of_bounded hSb (by fun_prop)) ?_
    refine (ae_restrict_iff' hSm).2 (Filter.Eventually.of_forall ?_)
    rintro ⟨w, z⟩ ⟨hw, hz⟩
    exact pairMean_pt hV hc1 hdlo hfirst (hseg w hw z hz) (heps w hw z hz) hU
  -- step 2: split the integral of `F`
  have i1 : IntegrableOn (fun p : Pt × Pt => U0 + gradTerm c 0 (-p.1 - c 0)) (Z ×ˢ Z') :=
    tp_integrableOn_of_bounded hSb (continuous_const.add cg0)
  have i2 : IntegrableOn (fun p : Pt × Pt => U0 + gradTerm c 0 (-p.1 - c 0) + gradTerm c 2 (p.2 - c 2)) (Z ×ˢ Z') :=
    tp_integrableOn_of_bounded hSb ((continuous_const.add cg0).add cg2)
  have i3 : IntegrableOn (fun p : Pt × Pt => U0 + gradTerm c 0 (-p.1 - c 0) + gradTerm c 2 (p.2 - c 2) +
      remTerm c eps dlo dhi first 0 1 (edist2 p.1 (-c 0))) (Z ×ˢ Z') :=
    tp_integrableOn_of_bounded hSb (((continuous_const.add cg0).add cg2).add cR01)
  have i4 : IntegrableOn (fun p : Pt × Pt => U0 + gradTerm c 0 (-p.1 - c 0) + gradTerm c 2 (p.2 - c 2) +
      remTerm c eps dlo dhi first 0 1 (edist2 p.1 (-c 0)) +
      remTerm c eps dlo dhi first 0 2 (edist2 p.1 (-c 0) + edist2 p.2 (c 2))) (Z ×ˢ Z') :=
    tp_integrableOn_of_bounded hSb ((((continuous_const.add cg0).add cg2).add cR01).add cR02)
  have hsplit : ∫ p in Z ×ˢ Z', (U0 + gradTerm c 0 (-p.1 - c 0) + gradTerm c 2 (p.2 - c 2) +
        remTerm c eps dlo dhi first 0 1 (edist2 p.1 (-c 0)) +
        remTerm c eps dlo dhi first 0 2 (edist2 p.1 (-c 0) + edist2 p.2 (c 2)) +
        remTerm c eps dlo dhi first 1 2 (edist2 p.2 (c 2))) =
      U0 * (V * V') + (∫ p in Z ×ˢ Z', gradTerm c 0 (-p.1 - c 0)) + (∫ p in Z ×ˢ Z', gradTerm c 2 (p.2 - c 2)) +
        (∫ p in Z ×ˢ Z', remTerm c eps dlo dhi first 0 1 (edist2 p.1 (-c 0))) +
        (∫ p in Z ×ˢ Z', remTerm c eps dlo dhi first 0 2 (edist2 p.1 (-c 0) + edist2 p.2 (c 2))) +
        (∫ p in Z ×ˢ Z', remTerm c eps dlo dhi first 1 2 (edist2 p.2 (c 2))) := by
    have hU0g : ∫ p in Z ×ˢ Z', (U0 + gradTerm c 0 (-p.1 - c 0)) =
        U0 * (V * V') + ∫ p in Z ×ˢ Z', gradTerm c 0 (-p.1 - c 0) := by
      have h := integral_add (μ := volume.restrict (Z ×ˢ Z')) (integrableOn_const (C := U0) hSt enorm_ne_top)
        (tp_integrableOn_of_bounded (μ := volume) hSb cg0)
      rw [h, setIntegral_const, measureReal_def, hS, smul_eq_mul, mul_comm]
    rw [integral_add i4 (tp_integrableOn_of_bounded hSb cR12), integral_add i3 (tp_integrableOn_of_bounded hSb cR02),
      integral_add i2 (tp_integrableOn_of_bounded hSb cR01), integral_add i1 (tp_integrableOn_of_bounded hSb cg2), hU0g]
  -- step 3: the gradient terms
  have hg0 : ∫ p in Z ×ˢ Z', gradTerm c 0 (-p.1 - c 0) ≤ 2 * e0 * (V * V') := by
    rw [tp_setIntegral_prod_fst' (fun w => gradTerm c 0 (-w - c 0)), integral_gradTerm_neg hZ0 hZt hZb, ← hVdef,
      ← hV'def]
    have h := gradTerm_le c 0 (-(cen Z) - c 0)
    rw [tp_enorm2_neg_sub] at h
    have : gradTerm c 0 (-(cen Z) - c 0) ≤ 2 * e0 := h.trans (by linarith)
    nlinarith
  have hg2 : ∫ p in Z ×ˢ Z', gradTerm c 2 (p.2 - c 2) ≤ 2 * e2 * (V * V') := by
    rw [tp_setIntegral_prod_snd' (fun z => gradTerm c 2 (z - c 2)), integral_gradTerm_sub hZ'0 hZ't hZ'b, ← hVdef,
      ← hV'def]
    have h := gradTerm_le c 2 (cen Z' - c 2)
    rw [tp_enorm2_sub_eq] at h
    have : gradTerm c 2 (cen Z' - c 2) ≤ 2 * e2 := h.trans (by linarith)
    nlinarith
  -- step 4: the remainder terms
  have hX0 : ∫ p in Z ×ˢ Z', edist2 p.1 (-c 0) = (∫ w in Z, edist2 w (-c 0)) * V' := by
    rw [tp_setIntegral_prod_fst' (fun w => edist2 w (-c 0)), ← hV'def]
  have hX2 : ∫ p in Z ×ˢ Z', edist2 p.2 (c 2) = V * ∫ z in Z', edist2 z (c 2) := by
    rw [tp_setIntegral_prod_snd' (fun z => edist2 z (c 2)), ← hVdef]
  have hX0s : ∫ p in Z ×ˢ Z', edist2 p.1 (-c 0) ^ 2 = (∫ w in Z, sqDist w (-c 0)) * V' := by
    rw [tp_setIntegral_prod_fst' (fun w => edist2 w (-c 0) ^ 2), ← hV'def, hsq0]
  have hX2s : ∫ p in Z ×ˢ Z', edist2 p.2 (c 2) ^ 2 = V * ∫ z in Z', sqDist z (c 2) := by
    rw [tp_setIntegral_prod_snd' (fun z => edist2 z (c 2) ^ 2), ← hVdef, hsq2]
  have hR01 := integral_remTerm_le (c := c) (eps := eps) (dlo := dlo) (dhi := dhi) (first := first) 0 1
    (S1 := √m0) (S2 := m0) hm iX0 iX0s
    (by rw [hX0]; nlinarith) (by rw [hX0s]; nlinarith) (hdlo 0 1 l01) (hμ 0 1 l01)
  have hR12 := integral_remTerm_le (c := c) (eps := eps) (dlo := dlo) (dhi := dhi) (first := first) 1 2
    (S1 := √m2) (S2 := m2) hm iX2 iX2s
    (by rw [hX2]; nlinarith) (by rw [hX2s]; nlinarith) (hdlo 1 2 l12) (hμ 1 2 l12)
  have hX02 : ∫ p in Z ×ˢ Z', (edist2 p.1 (-c 0) + edist2 p.2 (c 2)) ≤ (√m0 + √m2) * (V * V') := by
    rw [integral_add iX0 iX2, hX0, hX2]; nlinarith
  have hX02s : ∫ p in Z ×ˢ Z', (edist2 p.1 (-c 0) + edist2 p.2 (c 2)) ^ 2 ≤
      (m0 + m2 + 2 * √m0 * √m2) * (V * V') := by
    have e : ∀ p : Pt × Pt, (edist2 p.1 (-c 0) + edist2 p.2 (c 2)) ^ 2 =
        edist2 p.1 (-c 0) ^ 2 + edist2 p.2 (c 2) ^ 2 + 2 * (edist2 p.1 (-c 0) * edist2 p.2 (c 2)) := by
      intro p; ring
    have iP : IntegrableOn (fun p : Pt × Pt => edist2 p.1 (-c 0) * edist2 p.2 (c 2)) (Z ×ˢ Z') :=
      tp_integrableOn_of_bounded hSb (cX0.mul cX2)
    have iSS : IntegrableOn (fun p : Pt × Pt => edist2 p.1 (-c 0) ^ 2 + edist2 p.2 (c 2) ^ 2) (Z ×ˢ Z') :=
      iX0s.add iX2s
    rw [integral_congr_ae (Filter.Eventually.of_forall e), integral_add iSS (iP.const_mul 2),
      integral_add iX0s iX2s, integral_const_mul, hX0s, hX2s,
      tp_setIntegral_prod_mul' (fun w => edist2 w (-c 0)) (fun z => edist2 z (c 2))]
    have hp := mul_le_mul hZab hZ'ab hA2 (by positivity)
    nlinarith
  have hR02 := integral_remTerm_le (c := c) (eps := eps) (dlo := dlo) (dhi := dhi) (first := first) 0 2
    (S1 := √m0 + √m2) (S2 := m0 + m2 + 2 * √m0 * √m2) hm iX02 iX02s hX02 hX02s (hdlo 0 2 l02) (hμ 0 2 l02)
  -- step 5: the target
  have n10 : ¬ (1 : Fin 3) < 0 := by decide
  have n20 : ¬ (2 : Fin 3) < 0 := by decide
  have n21 : ¬ (2 : Fin 3) < 1 := by decide
  simp only [Fin.sum_univ_three, Fin.isValue, lt_self_iff_false, false_and, ↓reduceIte, l01, l02, l12, n10, n20,
    n21, true_and, add_zero, zero_add, pairS1, pairS2]
  simp (config := { decide := true }) only [↓reduceIte, Fin.isValue]
  have hfin : ∫ p in Z ×ˢ Z', unionArea ![-p.1, (0 : Pt), p.2] ≤
      U0 * (V * V') + 2 * e0 * (V * V') + 2 * e2 * (V * V') +
      (if dlo 0 1 < 2 then (nuCountSeg c eps dlo dhi first 0 1 : ℝ) *
        pairRem (dlo 0 1) (dhi 0 1) (first 0 1) √m0 m0 else 0) * (V * V') +
      (if dlo 0 2 < 2 then (nuCountSeg c eps dlo dhi first 0 2 : ℝ) *
        pairRem (dlo 0 2) (dhi 0 2) (first 0 2) (√m0 + √m2) (m0 + m2 + 2 * √m0 * √m2) else 0) * (V * V') +
      (if dlo 1 2 < 2 then (nuCountSeg c eps dlo dhi first 1 2 : ℝ) *
        pairRem (dlo 1 2) (dhi 1 2) (first 1 2) √m2 m2 else 0) * (V * V') := by
    rw [hsplit] at hstep1
    linarith
  convert hfin using 1
  ring

end BHH.W2
