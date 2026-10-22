/-
Module L: sorted coordinates (paper Lemma 4.1, the direction used):
`k! ∫_{H^{k-1}} ĝ(z) A(y(z))^{-s} dz ≤ ∫_{(ℝ²)^{k-1}} g(G_1(y)) A(y)^{-s} dy`.
-/
import W2.LapPerm

open MeasureTheory Set Real
open scoped ENNReal

noncomputable section

namespace BHH.W2

variable {m : ℕ}

/-! ## Linear maps on one real coordinate -/

/-- `Fin.cons 0 u` -/
def extR (u : Fin m → ℝ) : Fin (m + 1) → ℝ := Fin.cons 0 u

lemma extR_zero (u : Fin m → ℝ) : extR u 0 = 0 := rfl

lemma extR_succ (u : Fin m → ℝ) (l : Fin m) : extR u l.succ = u l := rfl

lemma extR_add (u v : Fin m → ℝ) (j : Fin (m + 1)) : extR (u + v) j = extR u j + extR v j := by
  refine Fin.cases ?_ (fun l => ?_) j
  · simp [extR]
  · simp [extR]

lemma extR_smul (c : ℝ) (u : Fin m → ℝ) (j : Fin (m + 1)) : extR (c • u) j = c * extR u j := by
  refine Fin.cases ?_ (fun l => ?_) j
  · simp [extR]
  · simp [extR]

/-- the relabeled configuration translated so that the point `σ 0` is at the origin (one real coordinate) -/
def relabR (σ : Equiv.Perm (Fin (m + 1))) : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ) where
  toFun u l := extR u (σ l.succ) - extR u (σ 0)
  map_add' u v := by funext l; simp only [extR_add, Pi.add_apply]; ring
  map_smul' c u := by funext l; simp only [extR_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

lemma relabR_apply (σ : Equiv.Perm (Fin (m + 1))) (u : Fin m → ℝ) (l : Fin m) :
    relabR σ u l = extR u (σ l.succ) - extR u (σ 0) := rfl

lemma extR_relabR (σ : Equiv.Perm (Fin (m + 1))) (u : Fin m → ℝ) (j : Fin (m + 1)) :
    extR (relabR σ u) j = extR u (σ j) - extR u (σ 0) := by
  refine Fin.cases ?_ (fun l => ?_) j
  · simp [extR_zero]
  · rw [extR_succ, relabR_apply]

lemma relabR_mul (σ τ : Equiv.Perm (Fin (m + 1))) : relabR τ ∘ₗ relabR σ = relabR (σ * τ) := by
  refine LinearMap.ext fun u => funext fun l => ?_
  rw [LinearMap.comp_apply, relabR_apply, relabR_apply, extR_relabR, extR_relabR, Equiv.Perm.mul_apply,
    Equiv.Perm.mul_apply]
  ring

lemma relabR_one : relabR (1 : Equiv.Perm (Fin (m + 1))) = LinearMap.id := by
  refine LinearMap.ext fun u => funext fun l => ?_
  rw [relabR_apply, Equiv.Perm.one_apply, Equiv.Perm.one_apply, extR_succ, extR_zero, sub_zero]
  rfl

lemma relabR_pow (σ : Equiv.Perm (Fin (m + 1))) (n : ℕ) : (relabR σ) ^ n = relabR (σ ^ n) := by
  induction n with
  | zero => rw [pow_zero, pow_zero, relabR_one]; rfl
  | succ n ih => rw [pow_succ', ih, Module.End.mul_eq_comp, relabR_mul, pow_succ]

lemma abs_det_relabR (σ : Equiv.Perm (Fin (m + 1))) : |LinearMap.det (relabR σ)| = 1 := by
  have hN := orderOf_pos σ
  have h1 : (relabR σ) ^ orderOf σ = 1 := by rw [relabR_pow, pow_orderOf_eq_one, relabR_one]; rfl
  have h2 : (LinearMap.det (relabR σ)) ^ orderOf σ = 1 := by rw [← map_pow, h1, map_one]
  have h3 : |LinearMap.det (relabR σ)| ^ orderOf σ = 1 := by rw [← abs_pow, h2, abs_one]
  exact (pow_eq_one_iff_of_nonneg (abs_nonneg _) hN.ne').1 h3

/-- the partial sums `u ↦ (Σ_{i ≤ l} u_i)_l` (one real coordinate) -/
def psR : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ) where
  toFun u l := ∑ i : Fin m, if i ≤ l then u i else 0
  map_add' u v := by
    funext l; simp only [Pi.add_apply]; rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by split_ifs <;> simp
  map_smul' c u := by
    funext l; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by split_ifs <;> simp

lemma psR_single (j l : Fin m) : psR (Pi.single j (1 : ℝ)) l = if j ≤ l then 1 else 0 := by
  show (∑ i : Fin m, if i ≤ l then Pi.single j (1 : ℝ) i else 0) = _
  rw [Finset.sum_eq_single j]
  · simp
  · intro i _ hij; simp [hij]
  · intro h; exact absurd (Finset.mem_univ j) h

lemma det_psR : LinearMap.det (psR (m := m)) = 1 := by
  rw [← LinearMap.det_toMatrix', Matrix.det_of_isLowerTriangular]
  · simp [LinearMap.toMatrix'_apply, psR_single]
  · intro i j hij
    simp only [LinearMap.toMatrix'_apply, psR_single]
    have : ¬ j ≤ i := not_le.2 hij
    simp [this]

/-! ## Measure preservation -/

lemma mp_of_absdet {f : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ)} (h : |LinearMap.det f| = 1) :
    MeasurePreserving f volume volume := by
  have hne : LinearMap.det f ≠ 0 := by
    intro h0; rw [h0, abs_zero] at h; exact zero_ne_one h
  refine ⟨f.continuous_of_finiteDimensional.measurable, ?_⟩
  rw [Measure.map_linearMap_addHaar_eq_smul_addHaar volume hne, abs_inv, h, _root_.inv_one, ENNReal.ofReal_one, one_smul]

/-- a linear map with nonzero determinant as a measurable equivalence -/
def lmEquiv (f : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ)) (hf : LinearMap.det f ≠ 0) : (Fin m → ℝ) ≃ᵐ (Fin m → ℝ) :=
  (LinearMap.equivOfDetNeZero f hf).toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv

lemma lmEquiv_coe (f : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ)) (hf : LinearMap.det f ≠ 0) : ⇑(lmEquiv f hf) = f := rfl

/-- a map on one real coordinate, applied to both coordinates of points of the plane -/
def liftPt (f : (Fin m → ℝ) → (Fin m → ℝ)) (w : Fin m → Pt) : Fin m → Pt :=
  fun i => (f (fun j => (w j).1) i, f (fun j => (w j).2) i)

/-- `liftPt` of a measurable equivalence -/
def liftEquiv (e : (Fin m → ℝ) ≃ᵐ (Fin m → ℝ)) : (Fin m → Pt) ≃ᵐ (Fin m → Pt) :=
  ((MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (Fin m)).trans (e.prodCongr e)).trans
    (MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (Fin m)).symm

lemma liftEquiv_coe (e : (Fin m → ℝ) ≃ᵐ (Fin m → ℝ)) : ⇑(liftEquiv e) = liftPt e := rfl

lemma mp_liftPt {f : (Fin m → ℝ) → (Fin m → ℝ)} (hf : MeasurePreserving f volume volume) :
    MeasurePreserving (liftPt f) volume volume := by
  have e1 := volume_measurePreserving_arrowProdEquivProdArrow ℝ ℝ (Fin m)
  have h2 : MeasurePreserving (Prod.map f f) (volume : Measure ((Fin m → ℝ) × (Fin m → ℝ))) volume :=
    hf.prod hf
  exact (e1.symm (MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (Fin m))).comp (h2.comp e1)

/-! ## The configuration maps on points of the plane -/

/-- partial sums: `PS z = (y_1, ..., y_m)` with `y_{l+1} = Σ_{i ≤ l} z_i` -/
def PS : (Fin m → Pt) → (Fin m → Pt) := liftPt psR

/-- the relabeled configuration translated to `σ 0` -/
def Cσ (σ : Equiv.Perm (Fin (m + 1))) : (Fin m → Pt) → (Fin m → Pt) := liftPt (relabR σ)

lemma cfg_fst (w : Fin m → Pt) (j : Fin (m + 1)) : (cfg w j).1 = extR (fun i => (w i).1) j := by
  refine Fin.cases ?_ (fun l => ?_) j
  · rfl
  · rfl

lemma cfg_snd (w : Fin m → Pt) (j : Fin (m + 1)) : (cfg w j).2 = extR (fun i => (w i).2) j := by
  refine Fin.cases ?_ (fun l => ?_) j
  · rfl
  · rfl

lemma cfg_Cσ (σ : Equiv.Perm (Fin (m + 1))) (w : Fin m → Pt) (j : Fin (m + 1)) :
    cfg (Cσ σ w) j = cfg w (σ j) - cfg w (σ 0) := by
  refine Prod.ext ?_ ?_
  · rw [cfg_fst, Prod.fst_sub, cfg_fst, cfg_fst]
    exact extR_relabR σ _ j
  · rw [cfg_snd, Prod.snd_sub, cfg_snd, cfg_snd]
    exact extR_relabR σ _ j

lemma cfg_PS (z : Fin m → Pt) : cfg (PS z) = psum z := by
  funext j
  refine Fin.cases ?_ (fun l => ?_) j
  · simp [cfg, psum]
  · show PS z l = psum z l.succ
    have hc : ∀ i : Fin m, (i.val < (l.succ : Fin (m + 1)).val) ↔ i ≤ l := by
      intro i; rw [Fin.val_succ, Fin.le_def]; omega
    unfold PS liftPt psum psR
    simp only [LinearMap.coe_mk, AddHom.coe_mk, hc]
    refine Prod.ext ?_ ?_
    · simp only [Prod.fst_sum]
      exact Finset.sum_congr rfl fun i _ => by split_ifs <;> rfl
    · simp only [Prod.snd_sum]
      exact Finset.sum_congr rfl fun i _ => by split_ifs <;> rfl

lemma det_relabR_ne (σ : Equiv.Perm (Fin (m + 1))) : LinearMap.det (relabR σ) ≠ 0 := by
  intro h; have := abs_det_relabR σ; rw [h, abs_zero] at this; exact zero_ne_one this

lemma det_psR_ne : LinearMap.det (psR (m := m)) ≠ 0 := by rw [det_psR]; exact one_ne_zero

lemma mp_PS : MeasurePreserving (PS (m := m)) volume volume := mp_liftPt (mp_of_absdet (by rw [det_psR, abs_one]))

lemma mp_Cσ (σ : Equiv.Perm (Fin (m + 1))) : MeasurePreserving (Cσ σ) volume volume :=
  mp_liftPt (mp_of_absdet (abs_det_relabR σ))

lemma memb_PS : MeasurableEmbedding (PS (m := m)) := by
  have := (liftEquiv (lmEquiv (psR (m := m)) det_psR_ne)).measurableEmbedding
  rwa [liftEquiv_coe, lmEquiv_coe] at this

lemma memb_Cσ (σ : Equiv.Perm (Fin (m + 1))) : MeasurableEmbedding (Cσ σ) := by
  have := (liftEquiv (lmEquiv (relabR σ) (det_relabR_ne σ))).measurableEmbedding
  rwa [liftEquiv_coe, lmEquiv_coe] at this

/-! ## Sorted configurations and the relabeled regions -/

/-- configurations whose `m + 1` points (`0` first) have strictly increasing first coordinates -/
def Sorted (m : ℕ) : Set (Fin m → Pt) := {u | StrictMono fun j => (cfg u j).1}

lemma measurable_cfg_apply (j : Fin (m + 1)) : Measurable fun u : Fin m → Pt => cfg u j := by
  refine Fin.cases ?_ (fun l => ?_) j
  · show Measurable fun _ : Fin m → Pt => (0 : Pt)
    exact measurable_const
  · show Measurable fun u : Fin m → Pt => u l
    exact measurable_pi_apply l

lemma measurableSet_Sorted : MeasurableSet (Sorted m) := by
  have : Sorted m = ⋂ i : Fin m, {u | (cfg u i.castSucc).1 < (cfg u i.succ).1} := by
    ext u
    simp only [mem_iInter]
    exact Fin.strictMono_iff_lt_succ
  rw [this]
  exact MeasurableSet.iInter fun i => measurableSet_lt (measurable_cfg_apply _).fst (measurable_cfg_apply _).fst

lemma preimage_PS_Sorted : PS ⁻¹' (Sorted m) = {z : Fin m → Pt | ∀ i, z i ∈ Hp} := by
  ext z
  show StrictMono (fun j => (cfg (PS z) j).1) ↔ ∀ i, z i ∈ Hp
  rw [cfg_PS, Fin.strictMono_iff_lt_succ]
  refine forall_congr' fun i => ?_
  have h' : psum z i.succ - psum z i.castSucc = z i := psum_succ_sub z i.isLt
  have h1 := congrArg Prod.fst h'
  simp only [Prod.fst_sub] at h1
  show _ ↔ 0 < (z i).1
  constructor <;> intro h <;> linarith

/-- the configurations that are sorted after relabeling by `σ` and translating `σ 0` to the origin -/
def Rσ (σ : Equiv.Perm (Fin (m + 1))) : Set (Fin m → Pt) := Cσ σ ⁻¹' Sorted m

lemma mem_Rσ (σ : Equiv.Perm (Fin (m + 1))) (w : Fin m → Pt) :
    w ∈ Rσ σ ↔ StrictMono fun j => (cfg w (σ j)).1 := by
  show StrictMono (fun j => (cfg (Cσ σ w) j).1) ↔ _
  simp only [cfg_Cσ, Prod.fst_sub]
  constructor
  · intro h i j hij
    have h2 : (cfg w (σ i)).1 - (cfg w (σ 0)).1 < (cfg w (σ j)).1 - (cfg w (σ 0)).1 := h hij
    show (cfg w (σ i)).1 < (cfg w (σ j)).1
    linarith
  · intro h i j hij
    have h2 : (cfg w (σ i)).1 < (cfg w (σ j)).1 := h hij
    show (cfg w (σ i)).1 - (cfg w (σ 0)).1 < (cfg w (σ j)).1 - (cfg w (σ 0)).1
    linarith

lemma Rσ_disjoint : Pairwise fun σ τ : Equiv.Perm (Fin (m + 1)) => Disjoint (Rσ σ) (Rσ τ) := by
  intro σ τ hστ
  refine Set.disjoint_left.2 fun w hσ hτ => hστ ?_
  rw [mem_Rσ] at hσ hτ
  have hr : Set.range (fun j => (cfg w (σ j)).1) = Set.range (fun j => (cfg w (τ j)).1) := by
    ext x
    constructor
    · rintro ⟨j, rfl⟩; exact ⟨τ.symm (σ j), by simp⟩
    · rintro ⟨j, rfl⟩; exact ⟨σ.symm (τ j), by simp⟩
  have he := (StrictMono.range_inj_of_wellFoundedLT hσ hτ).1 hr
  have hinj : Function.Injective fun i => (cfg w i).1 := by
    intro a b hab
    have h1 : σ.symm a = σ.symm b := hσ.injective (by simpa using hab)
    simpa using h1
  exact Equiv.ext fun j => hinj (congrFun he j)

/-! ## Sorted coordinates -/

/-- `Λ(H(y)) A(y)^{-s}` for the configuration `y = (0, u)` -/
def Gfun (s : ℝ) (u : Fin m → Pt) : ℝ := Lam (windowGraph (unitGraph (cfg u))) * unionArea (cfg u) ^ (-s)

lemma Gfun_PS (s : ℝ) (z : Fin m → Pt) : Gfun s (PS z) = ghat z * unionArea (psum z) ^ (-s) := by
  unfold Gfun ghat
  rw [cfg_PS]

lemma Gfun_Cσ_le (s : ℝ) (hm : 1 ≤ m) (σ : Equiv.Perm (Fin (m + 1))) (w : Fin m → Pt) :
    Gfun s (Cσ σ w) ≤ dcG (unitGraph (cfg w)) * unionArea (cfg w) ^ (-s) := by
  have hc : cfg (Cσ σ w) = fun j => cfg w (σ j) - cfg w (σ 0) := funext (cfg_Cσ σ w)
  unfold Gfun
  rw [hc, unitGraph_relabel, unionArea_relabel]
  exact mul_le_mul_of_nonneg_right (Lam_window_comap_le (by omega) _ σ)
    (Real.rpow_nonneg ENNReal.toReal_nonneg _)

/-- Lemma 4.1 (the direction used): `n! ∫_{H^m} ĝ(z) A(y(z))^{-s} dz ≤ ∫ g(G_1(y)) A(y)^{-s} dy`, `n = m + 1`. -/
theorem sorted_coords (s : ℝ) (hm : 1 ≤ m) (n : ℕ) (hn : n = m + 1) :
    (n.factorial : ℝ≥0∞) * ∫⁻ z in {z : Fin m → Pt | ∀ i, z i ∈ Hp},
        ENNReal.ofReal (ghat z * unionArea (psum z) ^ (-s)) ≤
      ∫⁻ w : Fin m → Pt, ENNReal.ofReal (dcG (unitGraph (cfg w)) * unionArea (cfg w) ^ (-s)) := by
  subst hn
  have hS := measurableSet_Sorted (m := m)
  have h1 : ∫⁻ z in {z : Fin m → Pt | ∀ i, z i ∈ Hp}, ENNReal.ofReal (ghat z * unionArea (psum z) ^ (-s)) =
      ∫⁻ u in Sorted m, ENNReal.ofReal (Gfun s u) := by
    have := mp_PS.setLIntegral_comp_preimage_emb memb_PS (fun u => ENNReal.ofReal (Gfun s u)) (Sorted m)
    rw [← this, preimage_PS_Sorted]
    simp only [Gfun_PS]
  have h2 : ∀ σ : Equiv.Perm (Fin (m + 1)), ∫⁻ u in Sorted m, ENNReal.ofReal (Gfun s u) ≤
      ∫⁻ w in Rσ σ, ENNReal.ofReal (dcG (unitGraph (cfg w)) * unionArea (cfg w) ^ (-s)) := by
    intro σ
    have := (mp_Cσ σ).setLIntegral_comp_preimage_emb (memb_Cσ σ) (fun u => ENNReal.ofReal (Gfun s u)) (Sorted m)
    rw [← this]
    exact lintegral_mono fun w => ENNReal.ofReal_le_ofReal (Gfun_Cσ_le s hm σ w)
  have hR : ∀ σ : Equiv.Perm (Fin (m + 1)), MeasurableSet (Rσ σ) := fun σ => (mp_Cσ σ).measurable hS
  calc ((m + 1).factorial : ℝ≥0∞) * ∫⁻ z in {z : Fin m → Pt | ∀ i, z i ∈ Hp},
          ENNReal.ofReal (ghat z * unionArea (psum z) ^ (-s))
      = ∑ _σ : Equiv.Perm (Fin (m + 1)), ∫⁻ u in Sorted m, ENNReal.ofReal (Gfun s u) := by
        rw [h1, Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]
    _ ≤ ∑ σ : Equiv.Perm (Fin (m + 1)),
          ∫⁻ w in Rσ σ, ENNReal.ofReal (dcG (unitGraph (cfg w)) * unionArea (cfg w) ^ (-s)) :=
        Finset.sum_le_sum fun σ _ => h2 σ
    _ = ∫⁻ w in ⋃ σ, Rσ σ, ENNReal.ofReal (dcG (unitGraph (cfg w)) * unionArea (cfg w) ^ (-s)) := by
        rw [lintegral_iUnion hR Rσ_disjoint, tsum_fintype]
    _ ≤ _ := setLIntegral_le_lintegral _ _

end BHH.W2
