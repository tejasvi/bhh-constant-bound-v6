/-
Invariances and measurability of the integrand of `C_k` (module E, item 2, part 1).

`Hint k y = g(G_1(y)) A(y)^{-(k - 1/2)}` (as an `ℝ≥0∞`) is measurable, invariant under permutations of the points
(Dong-Cao's `g` is invariant under graph isomorphisms) and under the rotations and the reflection of the plane
(they preserve distances and area).
-/
import BHH.Graph

open MeasureTheory Set Real
open scoped ENNReal

noncomputable section

namespace BHH.E

/-! ## `g` is invariant under graph isomorphisms -/

section Iso

variable {V W : Type*} [Fintype V] [Fintype W] {G : SimpleGraph V} {G' : SimpleGraph W}

omit [Fintype V] [Fintype W] in
lemma natCard_neighborSet_iso (φ : G ≃g G') (v : V) :
    Nat.card (G'.neighborSet (φ v)) = Nat.card (G.neighborSet v) :=
  Nat.card_congr (φ.mapNeighborSet v).symm

lemma dcD_iso (φ : G ≃g G') : dcD G = dcD G' := by
  unfold dcD
  simp only [degree_eq_natCard]
  congr 1
  exact Fintype.sum_equiv φ.toEquiv _ _ fun v => by
    rw [RelIso.coe_fn_toEquiv, natCard_neighborSet_iso]

lemma n1_iso (φ : G ≃g G') : n1 G = n1 G' := by
  classical
  unfold n1
  simp only [degree_eq_natCard]
  exact Finset.card_equiv φ.toEquiv fun v => by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [RelIso.coe_fn_toEquiv, natCard_neighborSet_iso]

/-- the subgraphs induced on the complements of `S` and of its image are isomorphic -/
def induceComplIso (φ : G ≃g G') (S : Finset V) :
    G.induce ((S : Set V)ᶜ) ≃g G'.induce (((S.map φ.toEquiv.toEmbedding : Finset W) : Set W)ᶜ) where
  toEquiv := φ.toEquiv.subtypeEquiv fun v => by
    simp only [mem_compl_iff, Finset.mem_coe, Finset.mem_map_equiv, Equiv.symm_apply_apply]
  map_rel_iff' := by
    intro a b
    simp only [SimpleGraph.comap_adj, Function.Embedding.coe_subtype, Equiv.subtypeEquiv_apply,
      RelIso.coe_fn_toEquiv]
    exact φ.map_adj_iff

omit [Fintype V] [Fintype W] in
lemma ccDel_iso (φ : G ≃g G') (S : Finset V) : ccDel G' (S.map φ.toEquiv.toEmbedding) = ccDel G S := by
  unfold ccDel
  exact Nat.card_congr (induceComplIso φ S).connectedComponentEquiv.symm

lemma dcQ_le_iso (φ : G ≃g G') : dcQ G ≤ dcQ G' := by
  unfold dcQ
  rw [n1_iso φ]
  refine max_le_max le_rfl (Finset.sup'_le _ _ fun S _ => ?_)
  rw [← ccDel_iso φ S, ← Finset.card_map φ.toEquiv.toEmbedding]
  exact Finset.le_sup' (fun T : Finset W => (ccDel G' T : ℤ) - T.card) (Finset.mem_univ _)

lemma dcQ_iso (φ : G ≃g G') : dcQ G = dcQ G' := le_antisymm (dcQ_le_iso φ) (dcQ_le_iso φ.symm)

theorem dcG_iso (φ : G ≃g G') : dcG G = dcG G' := by
  unfold dcG
  by_cases hc : G.Connected
  · rw [ite_eq_left hc, ite_eq_left (φ.connected_iff.mp hc), dcQ_iso φ, dcD_iso φ]
  · rw [ite_eq_right hc, ite_eq_right (fun h => hc (φ.connected_iff.mpr h))]

end Iso

/-! ## the integrand -/

/-- the integrand of `C_k` on configurations: `g(G_1(y)) A(y)^{-(k - 1/2)}` -/
def Hint (k : ℕ) (y : Fin k → Pt) : ℝ≥0∞ :=
  ENNReal.ofReal (dcG (unitGraph y) * unionArea y ^ (-((k : ℝ) - 1 / 2)))

lemma sqDist_comm (a b : Pt) : sqDist a b = sqDist b a := by unfold sqDist; ring

/-! ## permutations -/

/-- relabelling the points gives an isomorphic unit-distance graph -/
def unitGraphPermIso {k : ℕ} (y : Fin k → Pt) (τ : Equiv.Perm (Fin k)) :
    unitGraph (y ∘ τ) ≃g unitGraph y where
  toEquiv := τ
  map_rel_iff' := by
    intro i j
    simp only [unitGraph, Function.comp_apply, ne_eq, τ.injective.eq_iff]

lemma unionArea_perm {k : ℕ} (y : Fin k → Pt) (τ : Equiv.Perm (Fin k)) :
    unionArea (y ∘ τ) = unionArea y := by
  unfold unionArea
  congr 2
  exact τ.surjective.iUnion_comp fun i => disk (y i) 1

lemma Hint_perm {k : ℕ} (y : Fin k → Pt) (τ : Equiv.Perm (Fin k)) : Hint k (y ∘ τ) = Hint k y := by
  unfold Hint
  rw [dcG_iso (unitGraphPermIso y τ), unionArea_perm]

/-! ## isometries of the plane -/

lemma unitGraph_isom {k : ℕ} (R : Pt → Pt) (hR : ∀ a b, sqDist (R a) (R b) = sqDist a b)
    (y : Fin k → Pt) : unitGraph (fun i => R (y i)) = unitGraph y := by
  ext i j
  simp only [unitGraph, hR]

lemma unionArea_isom {k : ℕ} (R : Pt ≃ᵐ Pt) (hR : MeasurePreserving R)
    (hiso : ∀ a b, sqDist (R a) (R b) = sqDist a b) (y : Fin k → Pt) :
    unionArea (fun i => R (y i)) = unionArea y := by
  unfold unionArea
  have e : (⋃ i, disk (R (y i)) 1) = R.symm ⁻¹' (⋃ i, disk (y i) 1) := by
    ext z
    simp only [mem_iUnion, mem_preimage, disk]
    refine exists_congr fun i => ?_
    rw [mem_ofPred_eq, mem_ofPred_eq, ← hiso (R.symm z) (y i), R.apply_symm_apply]
  rw [e, (MeasurePreserving.symm R hR).measure_preimage_equiv]

lemma Hint_isom {k : ℕ} (R : Pt ≃ᵐ Pt) (hR : MeasurePreserving R)
    (hiso : ∀ a b, sqDist (R a) (R b) = sqDist a b) (y : Fin k → Pt) :
    Hint k (fun i => R (y i)) = Hint k y := by
  unfold Hint
  rw [unitGraph_isom R hiso, unionArea_isom R hR hiso]

/-- the rotation by `θ` -/
def rotP (θ : ℝ) (p : Pt) : Pt :=
  (Real.cos θ * p.1 - Real.sin θ * p.2, Real.sin θ * p.1 + Real.cos θ * p.2)

/-- the rotation by `θ` as a measurable equivalence (multiplication by `e^{iθ}` on `ℂ`) -/
def rotE (θ : ℝ) : Pt ≃ᵐ Pt :=
  (Complex.measurableEquivRealProd.symm.trans
    (rotation (Circle.exp θ)).toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv).trans
    Complex.measurableEquivRealProd

lemma rotE_apply (θ : ℝ) (p : Pt) : rotE θ p = rotP θ p := by
  simp only [rotE, MeasurableEquiv.trans_apply, Complex.measurableEquivRealProd_symm_apply,
    Homeomorph.toMeasurableEquiv_coe, ContinuousLinearEquiv.coe_toHomeomorph,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv, rotation_apply, Circle.coe_exp,
    Complex.measurableEquivRealProd_apply, rotP]
  rw [Complex.exp_mul_I]
  simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.cos_ofReal_re,
    Complex.cos_ofReal_im, Complex.sin_ofReal_re, Complex.sin_ofReal_im, Complex.I_re, Complex.I_im,
    Complex.mul_re, Complex.mul_im]
  ext <;> simp only <;> ring

lemma rotE_mp (θ : ℝ) : MeasurePreserving (rotE θ) :=
  Complex.volume_preserving_equiv_real_prod.comp
    ((rotation (Circle.exp θ)).measurePreserving.comp
      (MeasurePreserving.symm _ Complex.volume_preserving_equiv_real_prod))

lemma rotP_isom (θ : ℝ) (a b : Pt) : sqDist (rotP θ a) (rotP θ b) = sqDist a b := by
  unfold sqDist rotP
  linear_combination ((a.1 - b.1) ^ 2 + (a.2 - b.2) ^ 2) * Real.sin_sq_add_cos_sq θ

lemma rotE_isom (θ : ℝ) (a b : Pt) : sqDist (rotE θ a) (rotE θ b) = sqDist a b := by
  rw [rotE_apply, rotE_apply, rotP_isom]

/-- the reflection in the first axis -/
def reflE : Pt ≃ᵐ Pt := MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ) (MeasurableEquiv.neg ℝ)

lemma reflE_apply (p : Pt) : reflE p = (p.1, -p.2) := rfl

lemma reflE_mp : MeasurePreserving reflE :=
  (MeasurePreserving.id volume).prod (Measure.measurePreserving_neg volume)

lemma reflE_isom (a b : Pt) : sqDist (reflE a) (reflE b) = sqDist a b := by
  simp only [reflE_apply, sqDist]; ring

/-! ## configurations `(0, a, w)` -/

/-- the configuration `y_0 = 0`, `y_1 = a`, `y_{j+2} = w_j` -/
def cfg2 {m : ℕ} (a : Pt) (w : Fin m → Pt) : Fin (m + 2) → Pt := Fin.cons 0 (Fin.cons a w)

/-- a permutation of the last `m` points -/
def liftPerm2 {m : ℕ} (σ : Equiv.Perm (Fin m)) : Equiv.Perm (Fin (m + 2)) :=
  Equiv.Perm.decomposeFin.symm (0, Equiv.Perm.decomposeFin.symm (0, σ))

lemma cfg2_perm {m : ℕ} (a : Pt) (w : Fin m → Pt) (σ : Equiv.Perm (Fin m)) :
    cfg2 a (w ∘ σ) = cfg2 a w ∘ liftPerm2 σ := by
  funext i
  refine Fin.cases ?_ (fun i' => Fin.cases ?_ (fun j => ?_) i') i
  · simp [cfg2, liftPerm2, Equiv.Perm.decomposeFin_symm_apply_zero]
  · simp [cfg2, liftPerm2, Equiv.Perm.decomposeFin_symm_apply_zero]
  · simp [cfg2, liftPerm2, Equiv.Perm.decomposeFin_symm_apply_succ]

lemma cfg2_map {m : ℕ} (R : Pt → Pt) (h0 : R 0 = 0) (a : Pt) (w : Fin m → Pt) :
    (fun i => R (cfg2 a w i)) = cfg2 (R a) (fun j => R (w j)) := by
  funext i
  refine Fin.cases ?_ (fun i' => Fin.cases ?_ (fun j => ?_) i') i <;> simp [cfg2, h0]

lemma Hint_cfg2_perm {m : ℕ} (a : Pt) (w : Fin m → Pt) (σ : Equiv.Perm (Fin m)) :
    Hint (m + 2) (cfg2 a (w ∘ σ)) = Hint (m + 2) (cfg2 a w) := by
  rw [cfg2_perm, Hint_perm]

lemma rotE_zero (θ : ℝ) : rotE θ 0 = 0 := by
  rw [rotE_apply]; simp [rotP]

lemma Hint_cfg2_rot {m : ℕ} (θ : ℝ) (a : Pt) (w : Fin m → Pt) :
    Hint (m + 2) (cfg2 (rotE θ a) (fun j => rotE θ (w j))) = Hint (m + 2) (cfg2 a w) := by
  rw [← cfg2_map (rotE θ) (rotE_zero θ), Hint_isom (rotE θ) (rotE_mp θ) (rotE_isom θ)]

lemma Hint_cfg2_refl {m : ℕ} (r : ℝ) (w : Fin m → Pt) :
    Hint (m + 2) (cfg2 (r, 0) (fun j => reflE (w j))) = Hint (m + 2) (cfg2 (r, 0) w) := by
  have h0 : reflE 0 = 0 := by simp [reflE_apply]
  have hr : reflE (r, 0) = (r, 0) := by simp [reflE_apply]
  rw [← hr, ← cfg2_map reflE h0, Hint_isom reflE reflE_mp reflE_isom, hr]

/-! ## measurability -/

lemma measurable_sqDist {α : Type*} [MeasurableSpace α] {f g : α → Pt} (hf : Measurable f)
    (hg : Measurable g) : Measurable fun x => sqDist (f x) (g x) := by
  unfold sqDist
  fun_prop

lemma measurable_unionArea (k : ℕ) : Measurable fun y : Fin k → Pt => unionArea y := by
  set U : Set ((Fin k → Pt) × Pt) := ⋃ i, {p | sqDist p.2 (p.1 i) ≤ 1} with hU
  have hUm : MeasurableSet U :=
    MeasurableSet.iUnion fun i => measurableSet_le
      (measurable_sqDist measurable_snd ((measurable_pi_apply i).comp measurable_fst)) measurable_const
  have e : (fun y : Fin k → Pt => unionArea y) = fun y => (volume (Prod.mk y ⁻¹' U)).toReal := by
    funext y
    unfold unionArea
    congr 2
    ext z
    simp [hU, disk]
  rw [e]
  exact ENNReal.measurable_toReal.comp (measurable_measure_prodMk_left hUm)

/-- the graph of a Bool matrix -/
def boolGraph {k : ℕ} (b : Fin k × Fin k → Bool) : SimpleGraph (Fin k) where
  Adj i j := i ≠ j ∧ b (i, j) = true ∧ b (j, i) = true
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

lemma unitGraph_eq_boolGraph {k : ℕ} (y : Fin k → Pt) :
    unitGraph y = boolGraph (fun ij => decide (sqDist (y ij.1) (y ij.2) ≤ 1)) := by
  ext i j
  simp only [unitGraph, boolGraph, decide_eq_true_eq, sqDist_comm (y j) (y i), and_self]

lemma measurable_dcG_unitGraph (k : ℕ) : Measurable fun y : Fin k → Pt => dcG (unitGraph y) := by
  have hB : Measurable fun y : Fin k → Pt => fun ij : Fin k × Fin k => decide (sqDist (y ij.1) (y ij.2) ≤ 1) := by
    rw [measurable_pi_iff]
    intro ij
    apply measurable_to_bool
    have e : ((fun y : Fin k → Pt => decide (sqDist (y ij.1) (y ij.2) ≤ 1)) ⁻¹' {true}) =
        {y | sqDist (y ij.1) (y ij.2) ≤ 1} := by
      ext y; simp
    rw [e]
    exact measurableSet_le (measurable_sqDist (measurable_pi_apply _) (measurable_pi_apply _)) measurable_const
  have hF : Measurable fun b : Fin k × Fin k → Bool => dcG (boolGraph b) := measurable_of_countable _
  have h := hF.comp hB
  simp only [Function.comp_def, ← unitGraph_eq_boolGraph] at h
  exact h

lemma measurable_Hint (k : ℕ) : Measurable (Hint k) := by
  unfold Hint
  exact ENNReal.measurable_ofReal.comp
    ((measurable_dcG_unitGraph k).mul ((measurable_unionArea k).pow_const _))

lemma measurable_cfg2 {m : ℕ} : Measurable fun p : Pt × (Fin m → Pt) => cfg2 p.1 p.2 := by
  rw [measurable_pi_iff]
  intro i
  refine Fin.cases ?_ (fun i' => Fin.cases ?_ (fun j => ?_) i') i
  · simp only [cfg2, Fin.cons_zero]; exact measurable_const
  · simp only [cfg2, Fin.cons_succ, Fin.cons_zero]; exact measurable_fst
  · simp only [cfg2, Fin.cons_succ]; exact (measurable_pi_apply j).comp measurable_snd

end BHH.E
