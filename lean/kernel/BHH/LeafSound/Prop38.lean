/-
Module D: the Prop 3.8 branch of the leaf (`Prop38Spec`), pointwise on the box.

For `x` in the box, `y = xcfg k x`: every point is within `δ = deltaOf` of its rectangle centre, so `A(y)` is at most the
area of the union of the disks `B(c_i, 1 + δ)` (`EnlargedDisksProp`), which equals the union over the distinct centres
and is enclosed by `u` (`UnionSoundRProp`).  With `A(y) ≥ π`, `φ` decreasing, `r_2 ≥ lo_0 > 0` and `2g ≥ gmin`
(`gmin_le_two_g`), `F2 ≥ r_2 · 2g · φ(A(y)) ≥ fx(p38lb)`.
-/
import BHH.LeafSound.Specs
import BHH.LeafSound.UnionGlue
import BHH.LeafSound.RemPair
import BHH.LeafSound.BracketGlue
import BHH.Ivl.Phi

open BHH.Cert Real MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace BHH

namespace D38

/-! ## the distinct centres -/

lemma mem_foldl_distinct (p : ℤ × ℤ) : ∀ (l acc : List (ℤ × ℤ)),
    p ∈ l.foldl (fun acc c => if acc.contains c then acc else acc ++ [c]) acc ↔ p ∈ acc ∨ p ∈ l
  | [], acc => by simp
  | c :: l, acc => by
    rw [List.foldl_cons, mem_foldl_distinct p l]
    split_ifs with h
    · rw [List.contains_iff_mem] at h
      simp only [List.mem_cons]
      constructor
      · rintro (h1 | h1)
        · exact Or.inl h1
        · exact Or.inr (Or.inr h1)
      · rintro (h1 | h1 | h1)
        · exact Or.inl h1
        · subst h1; exact Or.inl h
        · exact Or.inr h1
    · simp only [List.mem_append, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false]
      tauto

lemma mem_distinctOf {p : ℤ × ℤ} {l : List (ℤ × ℤ)} : p ∈ distinctOf l ↔ p ∈ l := by
  unfold distinctOf
  rw [mem_foldl_distinct]
  simp

/-- the union of the disks at the points of a fixed-point list -/
lemma iUnion_ptsCfg {k : ℕ} (L : List (ℤ × ℤ)) (hk : L.length = k) (r : ℝ) :
    (⋃ i : Fin k, disk (ptsCfg k L i) r) = ⋃ p ∈ L, disk (fx p.1, fx p.2) r := by
  ext z
  simp only [mem_iUnion, exists_prop]
  constructor
  · rintro ⟨i, hi⟩
    have hil : i.val < L.length := by rw [hk]; exact i.isLt
    refine ⟨L[i.val], List.getElem_mem hil, ?_⟩
    unfold ptsCfg at hi
    rwa [List.getD_eq_getElem _ _ hil] at hi
  · rintro ⟨p, hp, hz⟩
    obtain ⟨n, hn, rfl⟩ := List.mem_iff_getElem.mp hp
    refine ⟨⟨n, by rw [← hk]; exact hn⟩, ?_⟩
    unfold ptsCfg
    simp only
    rwa [List.getD_eq_getElem _ _ hn]

/-! ## the largest half-diagonal -/

lemma le_foldl_max (l : List (Iv × Iv × Iv × Iv)) :
    ∀ acc : ℤ, acc ≤ l.foldl (fun acc (d, _, _, _) => Max.max acc d.hi) acc ∧
      ∀ e ∈ l, e.1.hi ≤ l.foldl (fun acc (d, _, _, _) => Max.max acc d.hi) acc := by
  induction l with
  | nil => intro acc; simp
  | cons e l ih =>
    intro acc
    obtain ⟨d, a, b, c⟩ := e
    simp only [List.foldl_cons]
    obtain ⟨h1, h2⟩ := ih (Max.max acc d.hi)
    refine ⟨le_trans (le_max_left _ _) h1, ?_⟩
    intro e he
    rcases List.mem_cons.mp he with rfl | he
    · exact le_trans (le_max_right _ _) h1
    · exact h2 e he

lemma deltaOf_nonneg (bx : List PtBox) : 0 ≤ deltaOf bx := (le_foldl_max _ 0).1

lemma moments_le_deltaOf {bx : List PtBox} {P : PtBox} (hP : P ∈ bx) : (moments P).1.hi ≤ deltaOf bx :=
  (le_foldl_max _ 0).2 _ (List.mem_map_of_mem hP)

lemma fx_le_fx' {a b : ℤ} (h : a ≤ b) : fx a ≤ fx b := by
  unfold fx; exact div_le_div_of_nonneg_right (by exact_mod_cast h) (by positivity)

lemma le_fx_hi {x : ℝ} {a : Iv} (h : ivMem x a) : x ≤ fx a.hi := by
  unfold fx; rw [le_div_iff₀ (by positivity)]; exact h.2

lemma fx_lo_le {x : ℝ} {a : Iv} (h : ivMem x a) : fx a.lo ≤ x := by
  unfold fx; rw [div_le_iff₀ (by positivity)]; exact h.1

/-! ## the branch -/

theorem prop38Spec_of {k : ℕ} (hk3 : 3 ≤ k) {gt : GTab} (hgt : GTabSound k gt) {cs : ℤ → Iv × Iv}
    (hcs : CosSinSound cs) (cand : CandFn) (hG : GreenFormula) (hUR : UnionSoundRProp)
    (hED : EnlargedDisksProp) (hPi : UnionAreaGePiProp) : Prop38Spec k gt cs cand := by
  intro lo hi hv hlo0 hgmin u hu x hx
  set gmin := gt.gmin (val3 (stCode k lo hi)) with hgmin_def
  set lo0 := listGet lo 0 with hlo0_def
  set delta := deltaOf (ptBoxes k lo hi) with hdelta
  set y := xcfg k x with hy
  -- the trivial case
  by_cases hp : p38lb k u lo0 gmin ≤ 0
  · rw [max_eq_right hp, fx_zero, ENNReal.ofReal_zero]; exact zero_le
  push Not at hp
  rw [max_eq_left hp.le]
  unfold p38lb at hp ⊢
  rcases hph : phiAt k u.A.hi with _ | ⟨f0, f1, f2⟩
  · exfalso
    simp only [hph] at hp
    simp [shrD] at hp
  simp only [hph] at hp ⊢
  obtain ⟨hApos, hf0, -, -⟩ := phiAt_sound k (by omega) u.A.hi f0 f1 f2 hph
  set s : ℝ := (k : ℝ) - 1 / 2 with hs
  have hs0 : 0 < s := by rw [hs]; have : (3 : ℝ) ≤ k := by exact_mod_cast hk3
                         linarith
  -- every point is within `δ` of its centre
  set c : Fin k → Pt := fun i => (boxRects k lo hi i).centre with hc
  have hδ : ∀ i, edist2 (y i) (c i) ≤ fx delta := by
    intro i
    have h1 := VertexRect.enorm2_sub_centre_le (mem_boxRects hx hk3 i)
    have h2 := (mom_enclosures hk3 hv i).1
    have h3 : (moments ((ptBoxes k lo hi).getD i.val default)).1.hi ≤ delta := by
      apply moments_le_deltaOf
      have hlen : i.val < (ptBoxes k lo hi).length := by simp [ptBoxes]
      rw [List.getD_eq_getElem _ _ hlen]
      exact List.getElem_mem hlen
    have e : edist2 (y i) (c i) = enorm2 (y i - c i) := by
      unfold edist2 enorm2 sqDist; simp only [Prod.fst_sub, Prod.snd_sub]
    rw [e]
    exact le_trans h1 (le_trans (le_fx_hi h2) (fx_le_fx' h3))
  obtain ⟨-, hA⟩ := hED k y c (fx delta) hδ
  -- the union over the distinct centres
  set L := ctrList k lo hi with hL
  have hLk : L.length = k := ctrList_length k lo hi
  have hcL : ∀ i, c i = ptsCfg k L i := fun i => (ptsCfg_ctrList hk3 hv i).symm
  set D := distinctOf L with hD
  have hdist : distinctOf ((ptBoxes k lo hi).map fun P => (P.xc, P.yc)) = D := rfl
  rw [hdist] at hu
  have hR : 0 < ONE + delta := by
    have := deltaOf_nonneg (ptBoxes k lo hi); unfold ONE; omega
  have hU := hUR hG cs hcs cand D.length D (ONE + delta) u rfl hR hu
  have hfxR : fx (ONE + delta) = 1 + fx delta := by
    unfold fx; push_cast; rw [ONE_cast]; field_simp
  have hunion : (⋃ i, disk (c i) (1 + fx delta)) = ⋃ i, disk (ptsCfg D.length D i) (fx (ONE + delta)) := by
    rw [hfxR]
    simp_rw [hcL]
    rw [iUnion_ptsCfg L hLk, iUnion_ptsCfg D rfl]
    ext z
    simp only [mem_iUnion, exists_prop, hD, mem_distinctOf]
  rw [hunion] at hA
  have hAy : unionArea y ≤ fx u.A.hi := le_trans hA (le_fx_hi hU)
  have hπ : π ≤ unionArea y := hPi k y (by omega)
  have hApos' : 0 < unionArea y := lt_of_lt_of_le Real.pi_pos hπ
  -- φ(A(y)) ≥ φ(fx u.A.hi) ≥ fx f0.lo
  have hphi : phiS s (fx u.A.hi) ≤ phiS s (unionArea y) := phi_anti hs0 hApos' hAy
  have hf0lo : fx f0.lo ≤ phiS s (fx u.A.hi) := by
    unfold phiS; rw [hs]; exact fx_lo_le hf0
  have hphi0 : 0 ≤ phiS s (fx u.A.hi) := by unfold phiS; exact Real.rpow_nonneg (le_of_lt hApos) _
  have hFnn : 0 ≤ fx (max f0.lo 0) := by
    unfold fx; exact div_nonneg (by exact_mod_cast le_max_right _ _) (by positivity)
  have hfmax : fx (max f0.lo 0) ≤ phiS s (unionArea y) := by
    have e : fx (max f0.lo 0) = max (fx f0.lo) 0 := by
      rcases le_total f0.lo 0 with h | h
      · have h' : fx f0.lo ≤ 0 := by
          unfold fx; exact div_nonpos_of_nonpos_of_nonneg (by exact_mod_cast h) (by positivity)
        rw [max_eq_right h, max_eq_right h', fx_zero]
      · have h' : 0 ≤ fx f0.lo := by
          unfold fx; exact div_nonneg (by exact_mod_cast h) (by positivity)
        rw [max_eq_left h, max_eq_left h']
    rw [e]; exact max_le (le_trans hf0lo hphi) (le_trans hphi0 hphi)
  have hm0 : 0 < mDim k := by unfold mDim; omega
  have hr2 : fx lo0 ≤ xget x 0 := by
    rw [mem_boxOf_iff] at hx
    have := (hx ⟨0, hm0⟩).1
    rw [xget_of_lt x hm0]; simpa [hlo0_def, listGet] using this
  have hlo0r : 0 < fx lo0 := by unfold fx; exact div_pos (by exact_mod_cast hlo0) (by positivity)
  have hg := gmin_le_two_g hk3 hgt hx
  have hgr : (0 : ℝ) < gmin := by exact_mod_cast hgmin
  -- the rounding
  have hround : fx (shrD (max f0.lo 0 * lo0 * gmin) PR) ≤ fx (max f0.lo 0) * fx lo0 * gmin := by
    have h := shrD_le (max f0.lo 0 * lo0 * gmin) PR
    have hS : (0 : ℝ) < 2 ^ PR := by positivity
    have e : ((max f0.lo 0 * lo0 * gmin : ℤ) : ℝ) / 2 ^ PR / 2 ^ PR = fx (max f0.lo 0) * fx lo0 * gmin := by
      unfold fx; push_cast; field_simp
    rw [← e]
    unfold fx
    exact div_le_div_of_nonneg_right h hS.le
  unfold F2
  apply ENNReal.ofReal_le_ofReal
  calc fx (shrD (max f0.lo 0 * lo0 * gmin) PR) ≤ fx (max f0.lo 0) * fx lo0 * gmin := hround
    _ ≤ phiS s (unionArea y) * xget x 0 * (2 * dcG (unitGraph (xcfg k x))) := by
        apply mul_le_mul (mul_le_mul hfmax hr2 hlo0r.le (le_trans hFnn hfmax)) hg hgr.le
        exact mul_nonneg (le_trans hFnn hfmax) (le_trans hlo0r.le hr2)
    _ = xget x 0 * (2 * dcG (unitGraph (xcfg k x))) * unionArea (xcfg k x) ^ (-((k : ℝ) - 1 / 2)) := by
        unfold phiS; rw [hs]; ring

end D38

end BHH
