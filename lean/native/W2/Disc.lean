/-
Module D: the discretisation bound `DiscBound g` (paper Section 4.4): `Ψ^d_k(t) ≤ Ψ_k(t)`.
-/
import W2.DiscGraph

open MeasureTheory Set Real ProbabilityTheory
open scoped ENNReal

noncomputable section

namespace BHH.W2

variable {g : GridR} (hNR : 0 < g.NR) (hNT : 0 < g.NT) {D : DiscData} {m : ℕ}

/-- the cells of a cell sequence -/
def cellsOf (c : CellSeq g m) : Fin m → Set Pt := fun j => g.cell (c j).1.val (c j).2.val

lemma measurable_zget (j : ℕ) : Measurable fun z : Fin m → Pt => zget z j := by
  unfold zget; split_ifs
  · exact measurable_pi_apply _
  · exact measurable_const

lemma measurable_Xsum : Measurable (Xsum (m := m)) := by
  have e : Xsum (m := m) = fun z => A1 (zget z 0) + ∑ j ∈ Finset.Ico 1 m, A2 (zget z (j - 1)) (zget z j) := rfl
  rw [e]
  have h1 : Measurable fun z : Fin m → Pt => A1 (zget z 0) := measurable_A1.comp (measurable_zget 0)
  have h2 : ∀ j ∈ Finset.Ico 1 m, Measurable fun z : Fin m → Pt => A2 (zget z (j - 1)) (zget z j) :=
    fun j _ => by
      simpa only [Function.comp_def] using
        measurable_A2.comp ((measurable_zget (m := m) (j - 1)).prodMk (measurable_zget j))
  exact h1.add (Finset.measurable_sum _ h2)

lemma Xsum_nonneg (z : Fin m → Pt) : 0 ≤ Xsum z :=
  add_nonneg (A1_nonneg _) (Finset.sum_nonneg fun _ _ => A2_nonneg _ _)

lemma Xsum_le (z : Fin m → Pt) : Xsum z ≤ π + m * π := by
  unfold Xsum
  have h1 := A1_le_pi (zget z 0)
  have h2 : ∑ j ∈ Finset.Ico 1 m, A2 (zget z (j - 1)) (zget z j) ≤ ∑ _j ∈ Finset.Ico 1 m, π :=
    Finset.sum_le_sum fun j _ => A2_le_pi _ _
  rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul] at h2
  have : ((m - 1 : ℕ) : ℝ) ≤ m := by exact_mod_cast Nat.sub_le m 1
  nlinarith [Real.pi_pos]

/-- the mean of the area bound over a product cell is at most the exponent of the tables -/
lemma integral_Xsum_le (hD : TableSound g D) (c : CellSeq g m) (hm : 1 ≤ m)
    (h0 : ∀ j, volume (cellsOf c j) ≠ 0) :
    ∫ z, Xsum z ∂unifPi (cellsOf c) ≤ expoSeq hNR hNT D c := by
  have ht : ∀ j, volume (cellsOf c j) ≠ ⊤ := fun j => g.volume_cell_ne_top _ _
  have hP := unifPi_isProb h0 ht
  have hvpos : ∀ j, 0 < (volume (cellsOf c j)).toReal := fun j => ENNReal.toReal_pos (h0 j) (ht j)
  have hz : ∀ (z : Fin m → Pt) (j : ℕ) (hj : j < m), zget z j = z ⟨j, hj⟩ := fun z j hj => by
    simp [zget, hj]
  -- integrability of the pieces
  have iA1 : ∀ f : (Fin m → Pt) → Pt, Measurable f → Integrable (fun z => A1 (f z)) (unifPi (cellsOf c)) :=
    fun f hf => Integrable.mono' (integrable_const π) (measurable_A1.comp hf).aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => by
        rw [Real.norm_eq_abs, abs_of_nonneg (A1_nonneg _)]; exact A1_le_pi _)
  have iA2 : ∀ f f' : (Fin m → Pt) → Pt, Measurable f → Measurable f' →
      Integrable (fun z => A2 (f z) (f' z)) (unifPi (cellsOf c)) :=
    fun f f' hf hf' => by
      have hm : Measurable fun z => A2 (f z) (f' z) := by
        simpa only [Function.comp_def] using measurable_A2.comp (hf.prodMk hf')
      exact Integrable.mono' (integrable_const π) hm.aestronglyMeasurable
        (Filter.Eventually.of_forall fun z => by
          rw [Real.norm_eq_abs, abs_of_nonneg (A2_nonneg _ _)]; exact A2_le_pi _ _)
  have hmz : ∀ j : ℕ, Measurable fun z : Fin m → Pt => zget z j := fun j => by
    unfold zget; split_ifs
    · exact measurable_pi_apply _
    · exact measurable_const
  unfold Xsum expoSeq
  rw [integral_add (iA1 _ (hmz 0)) (integrable_finsetSum _ fun j _ => iA2 _ _ (hmz _) (hmz _)),
    integral_finsetSum _ fun j _ => iA2 _ _ (hmz _) (hmz _)]
  refine add_le_add ?_ (Finset.sum_le_sum fun j hj => ?_)
  · -- the first step
    have h0m : 0 < m := hm
    simp_rw [hz _ 0 h0m]
    rw [integral_unifPi_eval h0 ht ⟨0, h0m⟩ measurable_A1, cget_of_lt hNR hNT c h0m]
    have hub := hD.ub (c ⟨0, h0m⟩).1.val (c ⟨0, h0m⟩).2.val (c ⟨0, h0m⟩).1.isLt (c ⟨0, h0m⟩).2.isLt
    rw [inv_mul_le_iff₀ (hvpos _)]
    simp only [cellsOf] at hub ⊢
    linarith [hub]
  · -- the pair steps
    obtain ⟨hj1, hjm⟩ := Finset.mem_Ico.1 hj
    have hj0 : j - 1 < m := by omega
    simp_rw [hz _ (j - 1) hj0, hz _ j hjm]
    have hne : (⟨j - 1, hj0⟩ : Fin m) ≠ ⟨j, hjm⟩ := by
      intro h; simp only [Fin.mk.injEq] at h; omega
    rw [integral_unifPi_pair h0 ht hne measurable_A2, cget_of_lt hNR hNT c hj0, cget_of_lt hNR hNT c hjm]
    have hab := hD.ab (c ⟨j - 1, hj0⟩).1.val (c ⟨j, hjm⟩).1.val (c ⟨j - 1, hj0⟩).2.val (c ⟨j, hjm⟩).2.val
      (c ⟨j - 1, hj0⟩).1.isLt (c ⟨j, hjm⟩).1.isLt (c ⟨j - 1, hj0⟩).2.isLt (c ⟨j, hjm⟩).2.isLt
    rw [inv_mul_le_iff₀ (mul_pos (hvpos _) (hvpos _))]
    unfold doff
    simp only [cellsOf] at hab ⊢
    linarith [hab]

/-- one product cell -/
lemma term_le (hD : TableSound g D) (c : CellSeq g m) (hm : 1 ≤ m) {t : ℝ} (ht : 0 ≤ t) :
    ENNReal.ofReal (((passVal2 (edgeA1 hNR hNT D c) (edgeA2 hNR hNT D c) (m + 1) : ℝ) / 2) *
        (∏ j, D.w (c j).1.val) * Real.exp (-(t * expoSeq hNR hNT D c))) ≤
      ∫⁻ z in Set.pi univ (cellsOf c), ENNReal.ofReal (ghat z * Real.exp (-(t * Xsum z))) := by
  set p : ℝ := (passVal2 (edgeA1 hNR hNT D c) (edgeA2 hNR hNT D c) (m + 1) : ℝ) / 2 with hpdef
  have hp0 : 0 ≤ p := by positivity
  have hw0 : ∀ j, 0 ≤ D.w (c j).1.val := fun j => hD.w_nonneg _
  have ht' : ∀ j, volume (cellsOf c j) ≠ ⊤ := fun j => g.volume_cell_ne_top _ _
  by_cases h0 : ∀ j, volume (cellsOf c j) ≠ 0
  swap
  · -- a cell of measure zero: the term vanishes
    push Not at h0
    obtain ⟨j, hj⟩ := h0
    have hwj : D.w (c j).1.val = 0 := by
      have := hD.w_le (c j).1.val (c j).2.val (c j).1.isLt (c j).2.isLt
      simp only [cellsOf] at hj
      rw [hj, ENNReal.toReal_zero] at this
      exact le_antisymm this (hw0 j)
    rw [Finset.prod_eq_zero (Finset.mem_univ j) hwj, mul_zero, zero_mul, ENNReal.ofReal_zero]
    exact zero_le
  have hP := unifPi_isProb h0 ht'
  have hmeasΩ : MeasurableSet (Set.pi univ (cellsOf c)) :=
    MeasurableSet.univ_pi fun j => g.measurableSet_cell hNT (c j).2.isLt
  set Ω := Set.pi univ (cellsOf c) with hΩdef
  have hvΩ : volume Ω = ∏ j, volume (cellsOf c j) := volume_pi_set _
  have hvΩt : volume Ω ≠ ⊤ := by rw [hvΩ]; exact ENNReal.prod_ne_top fun j _ => ht' j
  -- integrability of `e^{-tX}`
  have hEm : Measurable fun z : Fin m → Pt => Real.exp (-(t * Xsum z)) :=
    Real.measurable_exp.comp ((measurable_Xsum.const_mul t).neg)
  have hE01 : ∀ z : Fin m → Pt, 0 ≤ Real.exp (-(t * Xsum z)) ∧ Real.exp (-(t * Xsum z)) ≤ 1 := fun z =>
    ⟨(Real.exp_pos _).le, Real.exp_le_one_iff.2 (by nlinarith [Xsum_nonneg z])⟩
  have iE : Integrable (fun z => Real.exp (-(t * Xsum z))) (unifPi (cellsOf c)) :=
    Integrable.mono' (integrable_const 1) hEm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => by rw [Real.norm_eq_abs, abs_of_nonneg (hE01 z).1]; exact (hE01 z).2)
  have iX : Integrable (Xsum (m := m)) (unifPi (cellsOf c)) :=
    Integrable.mono' (integrable_const (π + m * π)) measurable_Xsum.aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => by rw [Real.norm_eq_abs, abs_of_nonneg (Xsum_nonneg z)]; exact Xsum_le z)
  -- Jensen
  have hJ : Real.exp (-(t * expoSeq hNR hNT D c)) ≤ ∫ z, Real.exp (-(t * Xsum z)) ∂unifPi (cellsOf c) := by
    have h1 := exp_integral_le (μ := unifPi (cellsOf c)) (X := fun z => -(t * Xsum z)) (iX.const_mul t).neg iE
    have h2 : ∫ z, -(t * Xsum z) ∂unifPi (cellsOf c) = -(t * ∫ z, Xsum z ∂unifPi (cellsOf c)) := by
      rw [integral_neg, integral_const_mul]
    rw [h2] at h1
    refine le_trans (Real.exp_le_exp.2 ?_) h1
    have := integral_Xsum_le hNR hNT hD c hm h0
    nlinarith
  -- the volume
  have hvol : ∏ j, D.w (c j).1.val ≤ (volume Ω).toReal := by
    rw [hvΩ, ENNReal.toReal_prod]
    exact Finset.prod_le_prod₀ (fun j _ => hw0 j) fun j _ => hD.w_le _ _ (c j).1.isLt (c j).2.isLt
  -- the integral over the product cell
  have hint : (volume Ω).toReal * Real.exp (-(t * expoSeq hNR hNT D c)) ≤
      ∫ z in Ω, Real.exp (-(t * Xsum z)) := by
    rw [restrict_pi_eq h0 ht', integral_smul_measure, smul_eq_mul]
    exact mul_le_mul_of_nonneg_left hJ ENNReal.toReal_nonneg
  have iEΩ : IntegrableOn (fun z => Real.exp (-(t * Xsum z))) Ω := by
    unfold IntegrableOn; rw [restrict_pi_eq h0 ht']; exact iE.smul_measure hvΩt
  calc ENNReal.ofReal (p * (∏ j, D.w (c j).1.val) * Real.exp (-(t * expoSeq hNR hNT D c)))
      ≤ ENNReal.ofReal (p * ((volume Ω).toReal * Real.exp (-(t * expoSeq hNR hNT D c)))) := by
        apply ENNReal.ofReal_le_ofReal
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hvol (Real.exp_pos _).le) hp0
    _ ≤ ENNReal.ofReal (p * ∫ z in Ω, Real.exp (-(t * Xsum z))) :=
        ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hint hp0)
    _ = ENNReal.ofReal p * ∫⁻ z in Ω, ENNReal.ofReal (Real.exp (-(t * Xsum z))) := by
        rw [ENNReal.ofReal_mul hp0, ofReal_integral_eq_lintegral_ofReal iEΩ
          (Filter.Eventually.of_forall fun z => (hE01 z).1)]
    _ = ∫⁻ z in Ω, ENNReal.ofReal (p * Real.exp (-(t * Xsum z))) := by
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        congr 1; ext z; rw [ENNReal.ofReal_mul hp0]
    _ ≤ ∫⁻ z in Ω, ENNReal.ofReal (ghat z * Real.exp (-(t * Xsum z))) := by
        refine setLIntegral_mono' hmeasΩ fun z hz => ENNReal.ofReal_le_ofReal ?_
        have hzc : ∀ j, z j ∈ g.cell (c j).1.val (c j).2.val := fun j => hz j (Set.mem_univ j)
        exact mul_le_mul_of_nonneg_right (pass_le_ghat hNR hNT hD c hzc hm) (hE01 z).1

/-- the discretisation bound -/
theorem discBound (g : GridR) : DiscBound g := by
  intro hNR hNT D hD m hm t ht
  have hm1 : 1 ≤ m := by omega
  set F : (Fin m → Pt) → ℝ≥0∞ := fun z => ENNReal.ofReal (ghat z * Real.exp (-(t * Xsum z))) with hF
  have hmeas : ∀ c : CellSeq g m, MeasurableSet (Set.pi univ (cellsOf c)) := fun c =>
    MeasurableSet.univ_pi fun j => g.measurableSet_cell hNT (c j).2.isLt
  have hdisj : Pairwise (Function.onFun Disjoint fun c : CellSeq g m => Set.pi univ (cellsOf c)) := by
    intro c c' hcc
    obtain ⟨j, hj⟩ : ∃ j, c j ≠ c' j := by
      by_contra h; push Not at h; exact hcc (funext h)
    rw [Function.onFun, Set.disjoint_left]
    intro z hz hz'
    have hd := g.cell_disjoint hNT (c j).2.isLt (c' j).2.isLt (ir := (c j).1.val) (ir' := (c' j).1.val)
      (fun he => hj (by
        simp only [Prod.mk.injEq] at he
        exact Prod.ext (Fin.ext he.1) (Fin.ext he.2)))
    exact Set.disjoint_left.1 hd (hz j (Set.mem_univ j)) (hz' j (Set.mem_univ j))
  have hsub : (⋃ c : CellSeq g m, Set.pi univ (cellsOf c)) ⊆ {z : Fin m → Pt | ∀ i, z i ∈ Hp} := by
    intro z hz
    obtain ⟨c, hc⟩ := Set.mem_iUnion.1 hz
    exact fun i => g.cell_subset_Hp hNT (c i).2.isLt (hc i (Set.mem_univ i))
  have hterm0 : ∀ c : CellSeq g m, 0 ≤ ((passVal2 (edgeA1 hNR hNT D c) (edgeA2 hNR hNT D c) (m + 1) : ℝ) / 2) *
      (∏ j, D.w (c j).1.val) * Real.exp (-(t * expoSeq hNR hNT D c)) := fun c => by
    have : 0 ≤ ∏ j, D.w (c j).1.val := Finset.prod_nonneg fun j _ => hD.w_nonneg _
    positivity
  unfold Psid Psi
  rw [ENNReal.ofReal_sum_of_nonneg fun c _ => hterm0 c]
  calc ∑ c : CellSeq g m, ENNReal.ofReal (((passVal2 (edgeA1 hNR hNT D c) (edgeA2 hNR hNT D c) (m + 1) : ℝ) / 2) *
          (∏ j, D.w (c j).1.val) * Real.exp (-(t * expoSeq hNR hNT D c)))
      ≤ ∑ c : CellSeq g m, ∫⁻ z in Set.pi univ (cellsOf c), F z :=
        Finset.sum_le_sum fun c _ => term_le hNR hNT hD c hm1 ht
    _ = ∫⁻ z in ⋃ c : CellSeq g m, Set.pi univ (cellsOf c), F z := by
        rw [lintegral_iUnion hmeas hdisj F, tsum_fintype]
    _ = ∫⁻ z in ⋃ c : CellSeq g m, Set.pi univ (cellsOf c),
          Set.indicator {z : Fin m → Pt | ∀ i, z i ∈ Hp} F z := by
        refine setLIntegral_congr_fun (MeasurableSet.iUnion hmeas) fun z hz => ?_
        rw [Set.indicator_of_mem (hsub hz)]
    _ ≤ ∫⁻ z, Set.indicator {z : Fin m → Pt | ∀ i, z i ∈ Hp} F z := setLIntegral_le_lintegral _ _

end BHH.W2
