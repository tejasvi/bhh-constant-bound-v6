/-
Coordinates of the box part (module E, item 2, part 2), for `k = n + 3`.

`coordE n : ℝ × (Fin (n+1) → Pt) ≃ᵐ (Fin (mDim (n+3)) → ℝ)` sends `(r, w)` to `x` with `x_0 = r`, `x_{2j+1} = ξ_j`,
`x_{2j+2} = η_j` (where `w_j = (ξ_j, η_j)` is the point `y_{j+2}`); it is measure preserving.  Under it,
`xcfg = cfg2 (r, 0) w`, `F2 = 2 r Hint`, and the strict version `DkS` of `D_k` is `Ioi 0 ×ˢ EstrictN n`; `D_k` lies
in `DkS` up to a null set (hyperplanes).
-/
import BHH.DomInv

open MeasureTheory Set Real
open scoped ENNReal

noncomputable section

namespace BHH.E

/-! ## the index equivalence -/

/-- `r ↦ 0`, `ξ_j ↦ 2j+1`, `η_j ↦ 2j+2` -/
def idxFun (n : ℕ) : Unit ⊕ (Fin (n + 1) ⊕ Fin (n + 1)) → Fin (mDim (n + 3))
  | .inl _ => ⟨0, by unfold mDim; omega⟩
  | .inr (.inl j) => ⟨2 * j.val + 1, by unfold mDim; omega⟩
  | .inr (.inr j) => ⟨2 * j.val + 2, by unfold mDim; omega⟩

lemma idxFun_injective (n : ℕ) : Function.Injective (idxFun n) := by
  rintro (_ | (a | a)) (_ | (b | b)) h <;> simp only [idxFun, Fin.mk.injEq] at h <;>
    first | rfl | omega | (congr 2; exact Fin.ext (by omega))

/-- the index equivalence -/
def idxEquiv (n : ℕ) : Unit ⊕ (Fin (n + 1) ⊕ Fin (n + 1)) ≃ Fin (mDim (n + 3)) :=
  Equiv.ofBijective (idxFun n) ((Fintype.bijective_iff_injective_and_card _).mpr
    ⟨idxFun_injective n, by
      simp only [Fintype.card_sum, Fintype.card_unit, Fintype.card_fin]
      unfold mDim; omega⟩)

/-! ## the coordinate map -/

/-- `(r, w) ↦ x` -/
def coordE (n : ℕ) : ℝ × (Fin (n + 1) → Pt) ≃ᵐ (Fin (mDim (n + 3)) → ℝ) :=
  ((((MeasurableEquiv.refl ℝ).prodCongr (MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (Fin (n + 1)))).trans
    ((MeasurableEquiv.refl ℝ).prodCongr
      (MeasurableEquiv.sumPiEquivProdPi fun _ : Fin (n + 1) ⊕ Fin (n + 1) => ℝ).symm)).trans
    ((MeasurableEquiv.funUnique Unit ℝ).symm.prodCongr (MeasurableEquiv.refl _))).trans
    ((MeasurableEquiv.sumPiEquivProdPi fun _ : Unit ⊕ (Fin (n + 1) ⊕ Fin (n + 1)) => ℝ).symm.trans
      (MeasurableEquiv.piCongrLeft (fun _ => ℝ) (idxEquiv n)))

lemma coordE_mp (n : ℕ) : MeasurePreserving (coordE n) := by
  have h1 := (MeasurePreserving.id (volume : Measure ℝ)).prod
    (volume_measurePreserving_arrowProdEquivProdArrow ℝ ℝ (Fin (n + 1)))
  have h2 := (MeasurePreserving.id (volume : Measure ℝ)).prod
    (volume_measurePreserving_sumPiEquivProdPi_symm fun _ : Fin (n + 1) ⊕ Fin (n + 1) => ℝ)
  have h3 := (MeasurePreserving.symm _ (volume_preserving_funUnique Unit ℝ)).prod
    (MeasurePreserving.id (volume : Measure (Fin (n + 1) ⊕ Fin (n + 1) → ℝ)))
  have h4 := volume_measurePreserving_sumPiEquivProdPi_symm fun _ : Unit ⊕ (Fin (n + 1) ⊕ Fin (n + 1)) => ℝ
  have h5 := volume_measurePreserving_piCongrLeft (fun _ => ℝ) (idxEquiv n)
  exact (h5.comp h4).comp (h3.comp (h2.comp h1))

lemma coordE_idx (n : ℕ) (p : ℝ × (Fin (n + 1) → Pt)) (i : Unit ⊕ (Fin (n + 1) ⊕ Fin (n + 1))) :
    coordE n p (idxEquiv n i) = Sum.elim (fun _ => p.1) (Sum.elim (fun j => (p.2 j).1) fun j => (p.2 j).2) i := by
  simp only [coordE, MeasurableEquiv.trans_apply, MeasurableEquiv.piCongrLeft_apply_apply]
  rcases i with _ | (j | j) <;> rfl

lemma coordE_zero (n : ℕ) (p : ℝ × (Fin (n + 1) → Pt)) (h : 0 < mDim (n + 3)) :
    coordE n p ⟨0, h⟩ = p.1 :=
  coordE_idx n p (.inl ())

lemma coordE_xi (n : ℕ) (p : ℝ × (Fin (n + 1) → Pt)) (j : Fin (n + 1)) (h : 2 * j.val + 1 < mDim (n + 3)) :
    coordE n p ⟨2 * j.val + 1, h⟩ = (p.2 j).1 :=
  coordE_idx n p (.inr (.inl j))

lemma coordE_eta (n : ℕ) (p : ℝ × (Fin (n + 1) → Pt)) (j : Fin (n + 1)) (h : 2 * j.val + 2 < mDim (n + 3)) :
    coordE n p ⟨2 * j.val + 2, h⟩ = (p.2 j).2 :=
  coordE_idx n p (.inr (.inr j))

lemma xget_coordE_zero (n : ℕ) (p : ℝ × (Fin (n + 1) → Pt)) : xget (coordE n p) 0 = p.1 := by
  have h : 0 < mDim (n + 3) := by unfold mDim; omega
  simp only [xget, h, dite_true]
  exact coordE_zero n p h

lemma xget_coordE_xi (n : ℕ) (p : ℝ × (Fin (n + 1) → Pt)) (j : ℕ) (hj : j < n + 1) :
    xget (coordE n p) (2 * j + 1) = (p.2 ⟨j, hj⟩).1 := by
  have h : 2 * j + 1 < mDim (n + 3) := by unfold mDim; omega
  simp only [xget, h, dite_true]
  exact coordE_xi n p ⟨j, hj⟩ h

lemma xget_coordE_eta (n : ℕ) (p : ℝ × (Fin (n + 1) → Pt)) (j : ℕ) (hj : j < n + 1) :
    xget (coordE n p) (2 * j + 2) = (p.2 ⟨j, hj⟩).2 := by
  have h : 2 * j + 2 < mDim (n + 3) := by unfold mDim; omega
  simp only [xget, h, dite_true]
  exact coordE_eta n p ⟨j, hj⟩ h

lemma xcfg_coordE (n : ℕ) (p : ℝ × (Fin (n + 1) → Pt)) :
    xcfg (n + 3) (coordE n p) = cfg2 (p.1, 0) p.2 := by
  funext i
  refine Fin.cases ?_ (fun i' => Fin.cases ?_ (fun j => ?_) i') i
  · simp [xcfg, cfg2]
  · simp [xcfg, cfg2, xget_coordE_zero]
  · simp only [xcfg, cfg2, Fin.cons_succ, Fin.val_succ]
    have e1 : 2 * (j.val + 1 + 1) - 3 = 2 * j.val + 1 := by omega
    have e2 : 2 * (j.val + 1 + 1) - 2 = 2 * j.val + 2 := by omega
    rw [e1, e2, xget_coordE_xi n p j.val j.isLt, xget_coordE_eta n p j.val j.isLt,
      ite_eq_right (by omega), ite_eq_right (by omega)]

lemma F2_coordE (n : ℕ) (p : ℝ × (Fin (n + 1) → Pt)) (hp : 0 ≤ p.1) :
    F2 (n + 3) (coordE n p) = ENNReal.ofReal p.1 * 2 * Hint (n + 3) (cfg2 (p.1, 0) p.2) := by
  unfold F2 Hint
  rw [xget_coordE_zero, xcfg_coordE]
  rw [show p.1 * (2 * dcG (unitGraph (cfg2 (p.1, 0) p.2))) *
      unionArea (cfg2 (p.1, 0) p.2) ^ (-((↑(n + 3) : ℝ) - 1 / 2)) =
      p.1 * (2 * (dcG (unitGraph (cfg2 (p.1, 0) p.2)) *
      unionArea (cfg2 (p.1, 0) p.2) ^ (-((↑(n + 3) : ℝ) - 1 / 2)))) by ring]
  rw [ENNReal.ofReal_mul hp, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat, mul_assoc]

/-! ## the domain -/

/-- the strict ordered region in the coordinates `w` -/
def EstrictN (n : ℕ) : Set (Fin (n + 1) → Pt) :=
  {w | 0 < (w 0).2 ∧ ∀ j : Fin n, (w j.castSucc).1 < (w j.succ).1}

/-- the strict version of `D_k` -/
def DkS (k : ℕ) : Set (Fin (mDim k) → ℝ) :=
  {x | 0 < xget x 0 ∧ 0 < xget x 2 ∧
    ∀ j : ℕ, 2 ≤ j → j + 1 < k → xget x (2 * j - 3) < xget x (2 * (j + 1) - 3)}

lemma measurableSet_EstrictN (n : ℕ) : MeasurableSet (EstrictN n) := by
  have e : EstrictN n = {w | 0 < (w 0).2} ∩ ⋂ j : Fin n, {w | (w j.castSucc).1 < (w j.succ).1} := by
    ext w; simp [EstrictN]
  rw [e]
  refine (measurableSet_lt measurable_const ((measurable_pi_apply 0).snd)).inter
    (MeasurableSet.iInter fun j => measurableSet_lt (measurable_pi_apply _).fst (measurable_pi_apply _).fst)

lemma coordE_mem_DkS (n : ℕ) (p : ℝ × (Fin (n + 1) → Pt)) :
    coordE n p ∈ DkS (n + 3) ↔ p ∈ Ioi (0 : ℝ) ×ˢ EstrictN n := by
  have hx2 : xget (coordE n p) 2 = (p.2 0).2 := by
    have := xget_coordE_eta n p 0 (by omega)
    simpa using this
  simp only [DkS, EstrictN, mem_ofPred_eq, mem_prod, mem_Ioi, xget_coordE_zero, hx2]
  refine and_congr Iff.rfl (and_congr Iff.rfl ?_)
  constructor
  · intro h j
    have := h (j.val + 2) (by omega) (by omega)
    have e1 : 2 * (j.val + 2) - 3 = 2 * j.val + 1 := by omega
    have e2 : 2 * (j.val + 2 + 1) - 3 = 2 * (j.val + 1) + 1 := by omega
    rw [e1, e2, xget_coordE_xi n p j.val (by omega), xget_coordE_xi n p (j.val + 1) (by omega)] at this
    exact this
  · intro h j hj1 hj2
    have := h ⟨j - 2, by omega⟩
    have e1 : 2 * j - 3 = 2 * (j - 2) + 1 := by omega
    have e2 : 2 * (j + 1) - 3 = 2 * (j - 2 + 1) + 1 := by omega
    rw [e1, e2, xget_coordE_xi n p (j - 2) (by omega), xget_coordE_xi n p (j - 2 + 1) (by omega)]
    exact this

/-- the hyperplanes on which `D_k` and its strict version differ -/
def Nset (n : ℕ) : Set (Fin (mDim (n + 3)) → ℝ) :=
  {x | xget x 0 = 0} ∪ {x | xget x 2 = 0} ∪ ⋃ j : Fin n, {x | xget x (2 * j.val + 1) = xget x (2 * j.val + 3)}

lemma Dk_subset (n : ℕ) : Dk (n + 3) ⊆ DkS (n + 3) ∪ Nset n := by
  intro x hx
  by_cases hN : x ∈ Nset n
  · exact Or.inr hN
  left
  simp only [Nset, mem_union, mem_ofPred_eq, mem_iUnion, not_or, not_exists] at hN
  obtain ⟨⟨h0, h2⟩, hj⟩ := hN
  obtain ⟨d0, d2, dj⟩ := hx
  refine ⟨lt_of_le_of_ne d0 (Ne.symm h0), lt_of_le_of_ne d2 (Ne.symm h2), fun j hj1 hj2 => ?_⟩
  refine lt_of_le_of_ne (dj j hj1 hj2) ?_
  have := hj ⟨j - 2, by omega⟩
  have e1 : 2 * (j - 2) + 1 = 2 * j - 3 := by omega
  have e2 : 2 * (j - 2) + 3 = 2 * (j + 1) - 3 := by omega
  simp only [e1, e2] at this
  exact this

lemma null_coord_eq_zero {m : ℕ} (d : Fin m) : volume {x : Fin m → ℝ | x d = 0} = 0 := by
  rw [volume_pi]
  exact Measure.pi_hyperplane _ d 0

lemma null_coord_eq {m : ℕ} (a b : Fin m) (hab : a ≠ b) : volume {x : Fin m → ℝ | x a = x b} = 0 := by
  let L : (Fin m → ℝ) →ₗ[ℝ] ℝ :=
    LinearMap.proj (R := ℝ) (φ := fun _ : Fin m => ℝ) a - LinearMap.proj (R := ℝ) (φ := fun _ : Fin m => ℝ) b
  have e : {x : Fin m → ℝ | x a = x b} = (LinearMap.ker L : Set (Fin m → ℝ)) := by
    ext x
    simp [L, sub_eq_zero]
  rw [e]
  apply Measure.addHaar_submodule
  intro htop
  have h1 : (Pi.single a (1 : ℝ) : Fin m → ℝ) ∈ LinearMap.ker L := by rw [htop]; exact Submodule.mem_top
  simp [L, hab.symm] at h1

lemma volume_Nset (n : ℕ) : volume (Nset n) = 0 := by
  have hm : ∀ (d : ℕ) (hd : d < mDim (n + 3)) (x : Fin (mDim (n + 3)) → ℝ), xget x d = x ⟨d, hd⟩ := by
    intro d hd x; simp [xget, hd]
  unfold Nset
  refine measure_union_null (measure_union_null ?_ ?_) (measure_iUnion_null fun j => ?_)
  · have h : 0 < mDim (n + 3) := by unfold mDim; omega
    have e : {x : Fin (mDim (n + 3)) → ℝ | xget x 0 = 0} = {x | x ⟨0, h⟩ = 0} := by
      ext x; rw [mem_ofPred_eq, mem_ofPred_eq, hm 0 h]
    rw [e]; exact null_coord_eq_zero _
  · have h : 2 < mDim (n + 3) := by unfold mDim; omega
    have e : {x : Fin (mDim (n + 3)) → ℝ | xget x 2 = 0} = {x | x ⟨2, h⟩ = 0} := by
      ext x; rw [mem_ofPred_eq, mem_ofPred_eq, hm 2 h]
    rw [e]; exact null_coord_eq_zero _
  · have ha : 2 * j.val + 1 < mDim (n + 3) := by unfold mDim; omega
    have hb : 2 * j.val + 3 < mDim (n + 3) := by unfold mDim; omega
    have e : {x : Fin (mDim (n + 3)) → ℝ | xget x (2 * j.val + 1) = xget x (2 * j.val + 3)} =
        {x | x ⟨2 * j.val + 1, ha⟩ = x ⟨2 * j.val + 3, hb⟩} := by
      ext x; rw [mem_ofPred_eq, mem_ofPred_eq, hm _ ha, hm _ hb]
    rw [e]
    exact null_coord_eq _ _ (by simp [Fin.ext_iff])

end BHH.E
