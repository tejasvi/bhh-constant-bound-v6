/-
Lemma 2.2, direction `≥` (module E, item 2): `DomainReductionProp k` for every `k ≥ 3`.

With `k = n + 3`, `y_0 = 0`, `y_1 = a`, and the other points `w : Fin (n+1) → Pt`:
`C_k = c_0 ∫ J(a) da` with `c_0 = Γ(k - 1/2)/(2 k!)` and `J(a) = ∫ Hint(0, a, w) dw`; polar coordinates for `a` and the
rotation invariance of `J` give `∫ J = 2π ∫_0^∞ r J((r, 0)) dr`; the `2 (n+1)!` images of the strict ordered region
`EstrictN n` under permutations of `w` and the reflection are pairwise disjoint and carry the same integral, so
`J((r, 0)) ≥ 2 (n+1)! ∫_{EstrictN} Hint`; finally the coordinates `x` of the box part are a measure-preserving change of
variables, `F2 = 2 r Hint`, and `D_k` lies in the strict region up to hyperplanes.
-/
import BHH.DomCoord

open MeasureTheory Set Real
open scoped ENNReal

noncomputable section

namespace BHH.E

/-! ## the inner integral `J` -/

/-- `J(a) = ∫ Hint(0, a, w) dw` -/
def Jfun (n : ℕ) (a : Pt) : ℝ≥0∞ := ∫⁻ w : Fin (n + 1) → Pt, Hint (n + 3) (cfg2 a w)

lemma measurable_Hint_cfg2 (n : ℕ) :
    Measurable fun p : Pt × (Fin (n + 1) → Pt) => Hint (n + 3) (cfg2 p.1 p.2) :=
  (measurable_Hint (n + 3)).comp measurable_cfg2

lemma measurable_Jfun (n : ℕ) : Measurable (Jfun n) :=
  (measurable_Hint_cfg2 n).lintegral_prod_right'

lemma C_eq (n : ℕ) : C (n + 3) =
    ENNReal.ofReal (Real.Gamma ((↑(n + 3) : ℝ) - 1 / 2) / (2 * ((n + 3).factorial : ℝ))) *
      ∫⁻ a : Pt, Jfun n a := by
  unfold C
  congr 1
  show ∫⁻ z : Fin (n + 2) → Pt, ENNReal.ofReal (ckIntegrand (n + 2) z) = ∫⁻ a : Pt, Jfun n a
  have h1 : ∀ z : Fin (n + 2) → Pt, ENNReal.ofReal (ckIntegrand (n + 2) z) = Hint (n + 3) (Fin.cons 0 z) := by
    intro z
    unfold ckIntegrand Hint cfg
    congr 3
    push_cast
    ring
  simp_rw [h1]
  have hmp := MeasurePreserving.symm _ (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 2) => Pt) 0)
  have e2 : ∀ p : Pt × (Fin (n + 1) → Pt),
      Hint (n + 3) (Fin.cons 0 ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 2) => Pt) 0).symm p)) =
        Hint (n + 3) (cfg2 p.1 p.2) := by
    intro p
    congr 1
    simp only [cfg2, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv_zero]
    rfl
  calc ∫⁻ z : Fin (n + 2) → Pt, Hint (n + 3) (Fin.cons 0 z)
      = ∫⁻ p : Pt × (Fin (n + 1) → Pt), Hint (n + 3)
          (Fin.cons 0 ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 2) => Pt) 0).symm p)) :=
        (hmp.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _)
          (fun z : Fin (n + 2) → Pt => Hint (n + 3) (Fin.cons 0 z))).symm
    _ = ∫⁻ p : Pt × (Fin (n + 1) → Pt), Hint (n + 3) (cfg2 p.1 p.2) := by simp_rw [e2]
    _ = ∫⁻ a : Pt, ∫⁻ w : Fin (n + 1) → Pt, Hint (n + 3) (cfg2 a w) := by
        rw [Measure.volume_eq_prod, lintegral_prod _ (measurable_Hint_cfg2 n).aemeasurable]
    _ = ∫⁻ a : Pt, Jfun n a := rfl

/-! ## rotation invariance and polar coordinates -/

/-- rotating all the points `w` -/
def rotPiE (n : ℕ) (θ : ℝ) : (Fin (n + 1) → Pt) ≃ᵐ (Fin (n + 1) → Pt) :=
  MeasurableEquiv.piCongrRight fun _ => rotE θ

lemma rotPiE_mp (n : ℕ) (θ : ℝ) : MeasurePreserving (rotPiE n θ) :=
  measurePreserving_pi (fun _ => volume) (fun _ => volume) fun _ => rotE_mp θ

lemma Jfun_rot (n : ℕ) (θ : ℝ) (a : Pt) : Jfun n (rotE θ a) = Jfun n a := by
  unfold Jfun
  have h := (rotPiE_mp n θ).lintegral_comp_emb (rotPiE n θ).measurableEmbedding
    (fun w => Hint (n + 3) (cfg2 (rotE θ a) w))
  rw [← h]
  congr 1
  funext w
  exact Hint_cfg2_rot θ a w

lemma lintegral_Jfun (n : ℕ) :
    ∫⁻ a : Pt, Jfun n a =
      (∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal r * Jfun n (r, 0)) * ENNReal.ofReal (2 * π) := by
  rw [← lintegral_comp_polarCoord_symm]
  have e : EqOn (fun q : ℝ × ℝ => ENNReal.ofReal q.1 • Jfun n (polarCoord.symm q))
      (fun q => ENNReal.ofReal q.1 * Jfun n (q.1, 0)) polarCoord.target := by
    intro q _
    have hq : polarCoord.symm q = rotE q.2 (q.1, 0) := by
      rw [rotE_apply]
      simp only [polarCoord_symm_apply, rotP, mul_zero, sub_zero, add_zero]
      ext <;> simp only <;> ring
    simp only [hq, Jfun_rot, smul_eq_mul]
  rw [setLIntegral_congr_fun polarCoord.open_target.measurableSet e, polarCoord_target,
    Measure.volume_eq_prod, ← Measure.prod_restrict, lintegral_prod _ ?_]
  · simp only [lintegral_const, Measure.restrict_apply_univ, Real.volume_Ioo]
    rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
    congr 2
    ring
  · exact ((ENNReal.measurable_ofReal.comp measurable_fst).mul
      ((measurable_Jfun n).comp (measurable_fst.prodMk measurable_const))).aemeasurable

/-! ## permutations and the reflection of the points `w` -/

/-- relabelling the points `w` -/
def permE {m : ℕ} (σ : Equiv.Perm (Fin m)) : (Fin m → Pt) ≃ᵐ (Fin m → Pt) where
  toFun w := w ∘ σ
  invFun w := w ∘ σ.symm
  left_inv w := by funext j; simp
  right_inv w := by funext j; simp
  measurable_toFun := measurable_pi_iff.mpr fun j => measurable_pi_apply (σ j)
  measurable_invFun := measurable_pi_iff.mpr fun j => measurable_pi_apply (σ.symm j)

lemma permE_mp {m : ℕ} (σ : Equiv.Perm (Fin m)) : MeasurePreserving (permE σ) := by
  have h := volume_measurePreserving_piCongrLeft (fun _ : Fin m => Pt) σ.symm
  have e : (permE σ : (Fin m → Pt) → (Fin m → Pt)) = MeasurableEquiv.piCongrLeft (fun _ => Pt) σ.symm := by
    funext w
    funext j
    have := MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ => Pt) σ.symm w (σ j)
    rw [Equiv.symm_apply_apply] at this
    exact this.symm
  rw [e]
  exact h

/-- reflecting all the points `w` (if `b`) -/
def reflPiE (m : ℕ) (b : Bool) : (Fin m → Pt) ≃ᵐ (Fin m → Pt) :=
  MeasurableEquiv.piCongrRight fun _ => cond b reflE (MeasurableEquiv.refl Pt)

lemma reflPiE_mp (m : ℕ) (b : Bool) : MeasurePreserving (reflPiE m b) :=
  measurePreserving_pi (fun _ => volume) (fun _ => volume) fun _ => by
    cases b
    · exact MeasurePreserving.id volume
    · exact reflE_mp

/-- the action of `(σ, b)` on the points `w` -/
def actE (n : ℕ) (g : Equiv.Perm (Fin (n + 1)) × Bool) : (Fin (n + 1) → Pt) ≃ᵐ (Fin (n + 1) → Pt) :=
  (permE g.1).trans (reflPiE (n + 1) g.2)

lemma actE_mp (n : ℕ) (g : Equiv.Perm (Fin (n + 1)) × Bool) : MeasurePreserving (actE n g) :=
  (reflPiE_mp _ _).comp (permE_mp _)

lemma actE_apply (n : ℕ) (g : Equiv.Perm (Fin (n + 1)) × Bool) (w : Fin (n + 1) → Pt) (j : Fin (n + 1)) :
    actE n g w j = cond g.2 (reflE (w (g.1 j))) (w (g.1 j)) := by
  rcases g with ⟨σ, b⟩
  cases b <;> rfl

lemma Hint_actE (n : ℕ) (r : ℝ) (g : Equiv.Perm (Fin (n + 1)) × Bool) (w : Fin (n + 1) → Pt) :
    Hint (n + 3) (cfg2 (r, 0) (actE n g w)) = Hint (n + 3) (cfg2 (r, 0) w) := by
  rcases g with ⟨σ, b⟩
  cases b
  · show Hint (n + 3) (cfg2 (r, 0) (w ∘ σ)) = _
    exact Hint_cfg2_perm _ w σ
  · show Hint (n + 3) (cfg2 (r, 0) (fun j => reflE ((w ∘ σ) j))) = _
    rw [Hint_cfg2_refl, Hint_cfg2_perm]

lemma actE_mem_iff (n : ℕ) (g : Equiv.Perm (Fin (n + 1)) × Bool) (w : Fin (n + 1) → Pt) :
    actE n g w ∈ EstrictN n ↔
      0 < cond g.2 (-(w (g.1 0)).2) (w (g.1 0)).2 ∧ StrictMono fun j => (w (g.1 j)).1 := by
  rw [Fin.strictMono_iff_lt_succ]
  simp only [EstrictN, mem_ofPred_eq, actE_apply]
  rcases g with ⟨σ, b⟩
  cases b <;> simp [reflE_apply]

/-- a list of distinct reals has only one sorting permutation -/
lemma perm_eq_of_strictMono {m : ℕ} (f : Fin m → ℝ) (σ σ' : Equiv.Perm (Fin m))
    (h : StrictMono fun j => f (σ j)) (h' : StrictMono fun j => f (σ' j)) : σ = σ' := by
  have hτ : StrictMono fun i => σ.symm (σ' i) := by
    intro i j hij
    have h1 := h' hij
    rw [← h.lt_iff_lt]
    simpa using h1
  have hsurj : Function.Surjective fun i => σ.symm (σ' i) := fun j => ⟨σ'.symm (σ j), by simp⟩
  refine Equiv.ext fun i => ?_
  have e := Fin.coe_orderIso_apply (StrictMono.orderIsoOfSurjective _ hτ hsurj) i
  simp only [StrictMono.coe_orderIsoOfSurjective] at e
  have hi : σ.symm (σ' i) = i := Fin.ext e
  calc σ i = σ (σ.symm (σ' i)) := by rw [hi]
    _ = σ' i := σ.apply_symm_apply _

lemma actE_disjoint (n : ℕ) :
    Set.PairwiseDisjoint (↑(Finset.univ : Finset (Equiv.Perm (Fin (n + 1)) × Bool)))
      fun g => actE n g ⁻¹' EstrictN n := by
  rintro ⟨σ, b⟩ _ ⟨σ', b'⟩ _ hne
  rw [Function.onFun, Set.disjoint_left]
  intro w hw hw'
  simp only [mem_preimage, actE_mem_iff] at hw hw'
  have hσ := perm_eq_of_strictMono (fun j => (w j).1) σ σ' hw.2 hw'.2
  subst hσ
  have hb : b ≠ b' := fun h => hne (by rw [h])
  obtain ⟨hw1, _⟩ := hw
  obtain ⟨hw1', _⟩ := hw'
  cases b <;> cases b' <;> simp only [Bool.cond_false, Bool.cond_true] at hw1 hw1' <;>
    first | exact hb rfl | linarith

lemma Jfun_ge (n : ℕ) (r : ℝ) :
    (2 * ((n + 1).factorial : ℝ≥0∞)) * ∫⁻ w in EstrictN n, Hint (n + 3) (cfg2 (r, 0) w) ≤ Jfun n (r, 0) := by
  set h : (Fin (n + 1) → Pt) → ℝ≥0∞ := fun w => Hint (n + 3) (cfg2 (r, 0) w) with hh
  have hA : ∀ g, ∫⁻ w in actE n g ⁻¹' EstrictN n, h w = ∫⁻ w in EstrictN n, h w := by
    intro g
    have e1 := (actE_mp n g).setLIntegral_comp_preimage_emb (actE n g).measurableEmbedding h (EstrictN n)
    rw [← e1]
    congr 1
    funext w
    exact (Hint_actE n r g w).symm
  have hm : ∀ g ∈ (Finset.univ : Finset (Equiv.Perm (Fin (n + 1)) × Bool)),
      MeasurableSet (actE n g ⁻¹' EstrictN n) :=
    fun g _ => (actE n g).measurable (measurableSet_EstrictN n)
  calc (2 * ((n + 1).factorial : ℝ≥0∞)) * ∫⁻ w in EstrictN n, h w
      = ∑ _g : Equiv.Perm (Fin (n + 1)) × Bool, ∫⁻ w in EstrictN n, h w := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_perm, Fintype.card_fin,
          Fintype.card_bool, nsmul_eq_mul]
        push_cast
        ring
    _ = ∑ g : Equiv.Perm (Fin (n + 1)) × Bool, ∫⁻ w in actE n g ⁻¹' EstrictN n, h w := by
        simp only [hA]
    _ = ∫⁻ w in ⋃ g ∈ (Finset.univ : Finset (Equiv.Perm (Fin (n + 1)) × Bool)), actE n g ⁻¹' EstrictN n,
          h w :=
        (lintegral_biUnion_finset (actE_disjoint n) hm h).symm
    _ ≤ ∫⁻ w, h w := setLIntegral_le_lintegral _ _

/-! ## the box coordinates -/

lemma lintegral_DkS (n : ℕ) :
    ∫⁻ x in DkS (n + 3), F2 (n + 3) x =
      ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal r * 2 * ∫⁻ w in EstrictN n, Hint (n + 3) (cfg2 (r, 0) w) := by
  have hpre : (coordE n) ⁻¹' DkS (n + 3) = Ioi (0 : ℝ) ×ˢ EstrictN n := by
    ext p
    simp only [mem_preimage]
    exact coordE_mem_DkS n p
  have hmeas : MeasurableSet (Ioi (0 : ℝ) ×ˢ EstrictN n) := measurableSet_Ioi.prod (measurableSet_EstrictN n)
  have e1 := (coordE_mp n).setLIntegral_comp_preimage_emb (coordE n).measurableEmbedding (F2 (n + 3)) (DkS (n + 3))
  rw [← e1, hpre]
  have e2 : EqOn (fun p => F2 (n + 3) (coordE n p))
      (fun p : ℝ × (Fin (n + 1) → Pt) => ENNReal.ofReal p.1 * 2 * Hint (n + 3) (cfg2 (p.1, 0) p.2))
      (Ioi (0 : ℝ) ×ˢ EstrictN n) := by
    intro p hp
    exact F2_coordE n p (le_of_lt hp.1)
  rw [setLIntegral_congr_fun hmeas e2, Measure.volume_eq_prod, ← Measure.prod_restrict, lintegral_prod _ ?_]
  · refine lintegral_congr fun r => ?_
    exact lintegral_const_mul' (ENNReal.ofReal r * 2) (fun w => Hint (n + 3) (cfg2 (r, 0) w))
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (by norm_num))
  · refine (((ENNReal.measurable_ofReal.comp measurable_fst).mul measurable_const).mul ?_).aemeasurable
    exact (measurable_Hint (n + 3)).comp
      (measurable_cfg2.comp ((measurable_fst.prodMk measurable_const).prodMk measurable_snd))

/-! ## Lemma 2.2 -/

theorem domainReduction (n : ℕ) : DomainReductionProp (n + 3) := by
  unfold DomainReductionProp
  set c0 : ℝ := Real.Gamma ((↑(n + 3) : ℝ) - 1 / 2) / (2 * ((n + 3).factorial : ℝ)) with hc0
  have hΓ : 0 < Real.Gamma ((↑(n + 3) : ℝ) - 1 / 2) := Real.Gamma_pos_of_pos (by push_cast; linarith)
  have hc0pos : 0 ≤ c0 := by positivity
  set I := ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal r * Jfun n (r, 0) with hI
  set S := ∫⁻ x in DkS (n + 3), F2 (n + 3) x with hS
  have h1 : ∫⁻ x in Dk (n + 3) ∩ Xk (n + 3), F2 (n + 3) x ≤ S := by
    calc ∫⁻ x in Dk (n + 3) ∩ Xk (n + 3), F2 (n + 3) x ≤ ∫⁻ x in DkS (n + 3) ∪ Nset n, F2 (n + 3) x :=
          lintegral_mono_set (inter_subset_left.trans (Dk_subset n))
      _ ≤ S + ∫⁻ x in Nset n, F2 (n + 3) x := lintegral_union_le _ _ _
      _ = S := by rw [setLIntegral_measure_zero _ _ (volume_Nset n), add_zero]
  have h2 : ((n + 1).factorial : ℝ≥0∞) * S ≤ I := by
    rw [hS, lintegral_DkS, ← lintegral_const_mul' _ _ (by simp)]
    refine setLIntegral_mono' measurableSet_Ioi fun r _ => ?_
    calc ((n + 1).factorial : ℝ≥0∞) *
          (ENNReal.ofReal r * 2 * ∫⁻ w in EstrictN n, Hint (n + 3) (cfg2 (r, 0) w))
        = ENNReal.ofReal r * ((2 * ((n + 1).factorial : ℝ≥0∞)) *
            ∫⁻ w in EstrictN n, Hint (n + 3) (cfg2 (r, 0) w)) := by ring
      _ ≤ ENNReal.ofReal r * Jfun n (r, 0) := mul_le_mul_right (Jfun_ge n r) _
  have hk : kappa (n + 3) / 2 = c0 * (2 * π) * ((n + 1).factorial : ℝ) := by
    unfold kappa
    rw [hc0, show n + 3 - 2 = n + 1 from rfl]
    have hf : ((n + 3).factorial : ℝ) = (n + 3) * (n + 2) * (n + 1).factorial := by
      rw [show n + 3 = (n + 1) + 1 + 1 from rfl, Nat.factorial_succ, Nat.factorial_succ]
      push_cast
      ring
    rw [hf]
    have : ((n + 1).factorial : ℝ) ≠ 0 := by positivity
    field_simp
  calc ENNReal.ofReal (kappa (n + 3) / 2) * ∫⁻ x in Dk (n + 3) ∩ Xk (n + 3), F2 (n + 3) x
      ≤ ENNReal.ofReal (kappa (n + 3) / 2) * S := mul_le_mul_right h1 _
    _ = ENNReal.ofReal (c0 * (2 * π)) * (((n + 1).factorial : ℝ≥0∞) * S) := by
        rw [hk, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast, mul_assoc]
    _ ≤ ENNReal.ofReal (c0 * (2 * π)) * I := mul_le_mul_right h2 _
    _ = ENNReal.ofReal c0 * (I * ENNReal.ofReal (2 * π)) := by
        rw [ENNReal.ofReal_mul hc0pos]
        ring
    _ = ENNReal.ofReal c0 * ∫⁻ a : Pt, Jfun n a := by rw [lintegral_Jfun]
    _ = C (n + 3) := (C_eq n).symm

/-- Lemma 2.2 (the direction used), for every `k ≥ 3`. -/
theorem domainReductionProp_of_three_le {k : ℕ} (hk : 3 ≤ k) : DomainReductionProp k := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 3 := ⟨k - 3, by omega⟩
  exact domainReduction n

end BHH.E

namespace BHH

-- the deliverables of this file, also under `BHH` (helpers stay in `BHH.E`)
export E (domainReduction domainReductionProp_of_three_le)

end BHH
