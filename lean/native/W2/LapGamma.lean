/-
Module L: measurability of `ĝ`, the Gamma integral in `[0, ∞]` form, and Tonelli
(paper Lemma 4.4, Laplace transform part).
-/
import W2.LapArea
import W2.Disc

open MeasureTheory Set Real
open scoped ENNReal

noncomputable section

namespace BHH.W2

variable {m : ℕ}

/-! ## Measurability of `ĝ` -/

lemma measurable_psum (i : Fin (m + 1)) : Measurable fun z : Fin m → Pt => psum z i := by
  unfold psum
  refine Finset.measurable_sum _ fun j _ => ?_
  split_ifs
  · exact measurable_pi_apply j
  · exact measurable_const

/-- the graph of a symmetric boolean relation -/
def graphB {n : ℕ} (b : Fin n → Fin n → Bool) : SimpleGraph (Fin n) where
  Adj i j := i ≠ j ∧ b i j = true ∧ b j i = true
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- the adjacency booleans of the configuration of partial sums -/
def adjB (z : Fin m → Pt) : Fin (m + 1) → Fin (m + 1) → Bool :=
  fun i j => decide (sqDist (psum z i) (psum z j) ≤ 1)

lemma unitGraph_psum_eq (z : Fin m → Pt) : unitGraph (psum z) = graphB (adjB z) := by
  ext i j
  simp only [unitGraph, graphB, adjB, decide_eq_true_eq]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, h2, ?_⟩
    unfold sqDist at h2 ⊢; nlinarith [h2]
  · rintro ⟨h1, h2, _⟩; exact ⟨h1, h2⟩

lemma measurable_adjB : Measurable (adjB (m := m)) := by
  refine measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun j => ?_
  refine measurable_to_countable' fun b => ?_
  have hS : MeasurableSet {z : Fin m → Pt | sqDist (psum z i) (psum z j) ≤ 1} := by
    refine measurableSet_le ?_ measurable_const
    unfold sqDist
    have hi := measurable_psum (m := m) i
    have hj := measurable_psum (m := m) j
    fun_prop
  cases b
  · have e : (fun z : Fin m → Pt => adjB z i j) ⁻¹' {false} = {z | sqDist (psum z i) (psum z j) ≤ 1}ᶜ := by
      ext z; simp [adjB]
    rw [e]; exact hS.compl
  · have e : (fun z : Fin m → Pt => adjB z i j) ⁻¹' {true} = {z | sqDist (psum z i) (psum z j) ≤ 1} := by
      ext z; simp [adjB]
    rw [e]; exact hS

lemma measurable_ghat : Measurable (ghat (m := m)) := by
  have e : ghat (m := m) = (fun b => Lam (windowGraph (graphB b))) ∘ adjB := by
    funext z; simp only [Function.comp, ghat, unitGraph_psum_eq]
  rw [e]
  exact (measurable_of_countable _).comp measurable_adjB

lemma ghat_nonneg (z : Fin m → Pt) : 0 ≤ ghat z := Lam_nonneg _

/-! ## The Gamma integral -/

lemma lintegral_gamma {s a : ℝ} (hs : 0 < s) (ha : 0 < a) :
    ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t ^ (s - 1) * Real.exp (-(a * t))) =
      ENNReal.ofReal (Real.Gamma s * a ^ (-s)) := by
  have hint : IntegrableOn (fun t : ℝ => t ^ (s - 1) * Real.exp (-(a * t))) (Ioi 0) := by
    have := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := s - 1) (b := a) (by linarith) one_pos ha
    refine this.congr_fun (fun t _ => ?_) measurableSet_Ioi
    simp only [Real.rpow_one, neg_mul]
  have hnn : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] fun t : ℝ => t ^ (s - 1) * Real.exp (-(a * t)) :=
    (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun t ht =>
      mul_nonneg (Real.rpow_nonneg (le_of_lt ht) _) (Real.exp_pos _).le)
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnn, integral_rpow_mul_exp_neg_mul_Ioi hs ha]
  congr 1
  rw [one_div, Real.inv_rpow ha.le, Real.rpow_neg ha.le, mul_comm]

/-! ## Tonelli -/

/-- the Laplace transform of `Ψ`: the left-hand side of `LaplaceBound` as one integral over the increments -/
theorem laplace_lhs_eq (k : ℕ) (hk : 3 ≤ k) :
    ENNReal.ofReal (1 / 2) *
      ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t ^ ((k : ℝ) - 3 / 2) * Real.exp (-(π * t))) * Psi (k - 1) t =
    ENNReal.ofReal (1 / 2) * ∫⁻ z, Set.indicator {z : Fin (k - 1) → Pt | ∀ i, z i ∈ Hp}
      (fun z => ENNReal.ofReal (ghat z * (Real.Gamma ((k : ℝ) - 1 / 2) * (π + Xsum z) ^ (-((k : ℝ) - 1 / 2))))) z := by
  congr 1
  set s : ℝ := (k : ℝ) - 1 / 2 with hsdef
  have hs : 0 < s := by have : (3 : ℝ) ≤ k := by exact_mod_cast hk
                        linarith
  have hs1 : (k : ℝ) - 3 / 2 = s - 1 := by rw [hsdef]; ring
  have hHm : MeasurableSet {z : Fin (k - 1) → Pt | ∀ i, z i ∈ Hp} := by
    have : {z : Fin (k - 1) → Pt | ∀ i, z i ∈ Hp} = ⋂ i, {z | 0 < (z i).1} := by ext z; simp [Hp]
    rw [this]
    exact MeasurableSet.iInter fun i => measurableSet_lt measurable_const ((measurable_pi_apply i).fst)
  -- push the `t`-weight inside the `z`-integral
  set F : ℝ → (Fin (k - 1) → Pt) → ℝ≥0∞ := fun t z => ENNReal.ofReal (t ^ ((k : ℝ) - 3 / 2) * Real.exp (-(π * t))) *
    Set.indicator {z : Fin (k - 1) → Pt | ∀ i, z i ∈ Hp}
      (fun z => ENNReal.ofReal (ghat z * Real.exp (-(t * Xsum z)))) z with hFdef
  have h1 : ∀ t, ENNReal.ofReal (t ^ ((k : ℝ) - 3 / 2) * Real.exp (-(π * t))) * Psi (k - 1) t =
      ∫⁻ z, F t z := fun t => by
    rw [Psi, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  simp_rw [h1]
  have hFm : Measurable (Function.uncurry F) := by
    refine Measurable.mul ?_ ?_
    · exact ENNReal.measurable_ofReal.comp ((measurable_fst.pow_const _).mul
        (Real.measurable_exp.comp ((measurable_fst.const_mul π).neg)))
    · refine Measurable.indicator ?_ (measurable_snd hHm)
      exact ENNReal.measurable_ofReal.comp ((measurable_ghat.comp measurable_snd).mul
        (Real.measurable_exp.comp ((measurable_fst.mul (measurable_Xsum.comp measurable_snd)).neg)))
  rw [lintegral_lintegral_swap hFm.aemeasurable]
  refine lintegral_congr fun z => ?_
  by_cases hz : z ∈ {z : Fin (k - 1) → Pt | ∀ i, z i ∈ Hp}
  · rw [Set.indicator_of_mem hz]
    have hX0 := Xsum_nonneg z
    have ha : 0 < π + Xsum z := by linarith [Real.pi_pos]
    have hg0 := ghat_nonneg z
    calc ∫⁻ t in Ioi (0 : ℝ), F t z
        = ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (ghat z) *
            ENNReal.ofReal (t ^ (s - 1) * Real.exp (-((π + Xsum z) * t))) := by
          refine setLIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
          simp only [hFdef, Set.indicator_of_mem hz]
          rw [← ENNReal.ofReal_mul (mul_nonneg (Real.rpow_nonneg (le_of_lt ht) _) (Real.exp_pos _).le),
            ← ENNReal.ofReal_mul hg0, hs1]
          congr 1
          rw [show -((π + Xsum z) * t) = -(π * t) + -(t * Xsum z) by ring, Real.exp_add]
          ring
      _ = ENNReal.ofReal (ghat z) * ENNReal.ofReal (Real.Gamma s * (π + Xsum z) ^ (-s)) := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_gamma hs ha]
      _ = ENNReal.ofReal (ghat z * (Real.Gamma s * (π + Xsum z) ^ (-s))) := (ENNReal.ofReal_mul hg0).symm
  · rw [Set.indicator_of_notMem hz]
    have : ∀ t, F t z = 0 := fun t => by simp only [hFdef, Set.indicator_of_notMem hz, mul_zero]
    simp only [this, lintegral_zero]

end BHH.W2
