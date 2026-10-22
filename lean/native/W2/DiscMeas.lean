/-
Module D: measure theory for the discretisation bound.
* the uniform probability measure on a product of sets of the plane, its relation to the volume, its one- and
  two-coordinate marginals;
* measurability and bounds of `A1`, `A2`;
* Jensen's inequality for `exp`.
-/
import W2.Defs

open MeasureTheory Set Real ProbabilityTheory
open scoped ENNReal

noncomputable section

namespace BHH.W2

/-! ## The uniform probability measure on a set of finite positive measure -/

/-- the uniform probability measure on `S` (`S` of finite positive measure) -/
def unifOn {α : Type*} [MeasurableSpace α] (μ : Measure α) (S : Set α) : Measure α := (μ S)⁻¹ • μ.restrict S

lemma unifOn_isProb {α : Type*} [MeasurableSpace α] {μ : Measure α} {S : Set α} (h0 : μ S ≠ 0)
    (ht : μ S ≠ ⊤) : IsProbabilityMeasure (unifOn μ S) := by
  constructor
  rw [unifOn, Measure.smul_apply, Measure.restrict_apply MeasurableSet.univ, univ_inter, smul_eq_mul]
  exact ENNReal.inv_mul_cancel h0 ht

lemma restrict_eq_smul_unifOn {α : Type*} [MeasurableSpace α] {μ : Measure α} {S : Set α} (h0 : μ S ≠ 0)
    (ht : μ S ≠ ⊤) : μ.restrict S = μ S • unifOn μ S := by
  rw [unifOn, smul_smul, ENNReal.mul_inv_cancel h0 ht, one_smul]

lemma integral_unifOn {α : Type*} [MeasurableSpace α] {μ : Measure α} {S : Set α} (f : α → ℝ) :
    ∫ x, f x ∂unifOn μ S = (μ S).toReal⁻¹ * ∫ x in S, f x ∂μ := by
  rw [unifOn, integral_smul_measure, smul_eq_mul, ENNReal.toReal_inv]

/-! ## Products of sets of the plane -/

variable {m : ℕ}

/-- the product measure of the uniform measures on the sets `S j` -/
def unifPi (S : Fin m → Set Pt) : Measure (Fin m → Pt) := Measure.pi fun j => unifOn volume (S j)

lemma unifPi_isProb {S : Fin m → Set Pt} (h0 : ∀ j, volume (S j) ≠ 0) (ht : ∀ j, volume (S j) ≠ ⊤) :
    IsProbabilityMeasure (unifPi S) := by
  have : ∀ j, IsProbabilityMeasure (unifOn volume (S j)) := fun j => unifOn_isProb (h0 j) (ht j)
  unfold unifPi; infer_instance

lemma volume_pi_set (S : Fin m → Set Pt) : volume (Set.pi univ S) = ∏ j, volume (S j) := by
  rw [volume_pi, Measure.pi_pi]

/-- the volume restricted to a product set is its volume times the uniform product measure -/
lemma restrict_pi_eq {S : Fin m → Set Pt} (h0 : ∀ j, volume (S j) ≠ 0) (ht : ∀ j, volume (S j) ≠ ⊤) :
    volume.restrict (Set.pi univ S) = volume (Set.pi univ S) • unifPi S := by
  have : ∀ j, IsProbabilityMeasure (unifOn volume (S j)) := fun j => unifOn_isProb (h0 j) (ht j)
  rw [volume_pi_set, volume_pi, Measure.restrict_pi_pi]
  refine Measure.pi_eq fun s hs => ?_
  rw [Measure.smul_apply, unifPi, Measure.pi_pi, smul_eq_mul, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [restrict_eq_smul_unifOn (h0 j) (ht j), Measure.smul_apply, smul_eq_mul]

lemma unifPi_ae_mem {S : Fin m → Set Pt} (hS : ∀ j, MeasurableSet (S j)) (h0 : ∀ j, volume (S j) ≠ 0)
    (ht : ∀ j, volume (S j) ≠ ⊤) : ∀ᵐ z ∂unifPi S, z ∈ Set.pi univ S := by
  have hne : volume (Set.pi univ S) ≠ 0 := by
    rw [volume_pi_set]; exact Finset.prod_ne_zero_iff.2 fun j _ => h0 j
  have hnt : volume (Set.pi univ S) ≠ ⊤ := by
    rw [volume_pi_set]; exact ENNReal.prod_ne_top fun j _ => ht j
  have e : unifPi S = (volume (Set.pi univ S))⁻¹ • volume.restrict (Set.pi univ S) := by
    rw [restrict_pi_eq h0 ht, smul_smul, ENNReal.inv_mul_cancel hne hnt, one_smul]
  rw [e]
  exact Measure.ae_smul_measure (ae_restrict_mem (MeasurableSet.univ_pi hS)) _

/-- one-coordinate marginal -/
lemma integral_unifPi_eval {S : Fin m → Set Pt} (h0 : ∀ j, volume (S j) ≠ 0) (ht : ∀ j, volume (S j) ≠ ⊤)
    (j : Fin m) {f : Pt → ℝ} (hf : Measurable f) :
    ∫ z, f (z j) ∂unifPi S = (volume (S j)).toReal⁻¹ * ∫ p in S j, f p := by
  have : ∀ j, IsProbabilityMeasure (unifOn volume (S j)) := fun j => unifOn_isProb (h0 j) (ht j)
  have hmap : (unifPi S).map (fun z => z j) = unifOn volume (S j) := (measurePreserving_eval _ j).map_eq
  rw [← integral_unifOn, ← hmap, integral_map (measurable_pi_apply j).aemeasurable hf.aestronglyMeasurable]

/-- two-coordinate marginal (`i ≠ j`) -/
lemma integral_unifPi_pair {S : Fin m → Set Pt} (h0 : ∀ j, volume (S j) ≠ 0) (ht : ∀ j, volume (S j) ≠ ⊤)
    {i j : Fin m} (hij : i ≠ j) {F : Pt × Pt → ℝ} (hF : Measurable F) :
    ∫ z, F (z i, z j) ∂unifPi S =
      ((volume (S i)).toReal * (volume (S j)).toReal)⁻¹ * ∫ q in S i ×ˢ S j, F q := by
  have hP : ∀ j, IsProbabilityMeasure (unifOn volume (S j)) := fun j => unifOn_isProb (h0 j) (ht j)
  have hPi := unifPi_isProb h0 ht
  have hind : iIndepFun (fun j (z : Fin m → Pt) => z j) (unifPi S) :=
    iIndepFun_pi (X := fun _ => id) fun _ => aemeasurable_id
  have h2 := (hind.indepFun hij).map_prod_eq_prod_map_map (measurable_pi_apply i).aemeasurable
    (measurable_pi_apply j).aemeasurable
  have hmi : (unifPi S).map (fun z => z i) = unifOn volume (S i) := (measurePreserving_eval _ i).map_eq
  have hmj : (unifPi S).map (fun z => z j) = unifOn volume (S j) := (measurePreserving_eval _ j).map_eq
  rw [hmi, hmj] at h2
  rw [← integral_map ((measurable_pi_apply i).prodMk (measurable_pi_apply j)).aemeasurable
    hF.aestronglyMeasurable]
  change ∫ q, F q ∂(unifPi S).map (fun z => (z i, z j)) = _
  rw [h2, unifOn, unifOn, Measure.prod_smul_left, Measure.prod_smul_right, Measure.prod_restrict,
    ← Measure.volume_eq_prod, integral_smul_measure, integral_smul_measure, smul_eq_mul, smul_eq_mul,
    ENNReal.toReal_inv, ENNReal.toReal_inv, mul_inv]
  ring

/-! ## Jensen's inequality for `exp` -/

lemma exp_integral_le {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ] {X : α → ℝ}
    (hX : Integrable X μ) (hE : Integrable (fun x => Real.exp (X x)) μ) :
    Real.exp (∫ x, X x ∂μ) ≤ ∫ x, Real.exp (X x) ∂μ :=
  convexOn_exp.map_integral_le continuous_exp.continuousOn isClosed_univ (Filter.Eventually.of_forall
    fun _ => mem_univ _) hX hE

end BHH.W2
