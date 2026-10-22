/-
Module C: the staircase bounds for the edge events on a box (`StripRealProp`, measure-theoretic part of
`ProbStripsProp`).
-/
import BHH.Box.Edge
import BHH.Box.StripDefs

open MeasureTheory Set Real ProbabilityTheory
open scoped ENNReal

noncomputable section

namespace BHH

open BHH.Cert

/-! ## End values and monotonicity of `cdfR` -/

lemma cdfR_left {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d) (hnd : a < b ∨ c < d) :
    cdfR a b c d (a - d) = 0 := by
  rcases eq_or_lt_of_le hab with hab' | hab' <;> rcases eq_or_lt_of_le hcd with hcd' | hcd'
  · subst hab' hcd'; simp at hnd
  · subst hab'; simp [cdfR, hcd'.ne]
  · subst hcd'; simp [cdfR, hab'.ne]
  · rw [cdfR_piece hab' hcd']; simp

lemma cdfR_right {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d) : cdfR a b c d (b - c) = 1 := by
  rcases eq_or_lt_of_le hab with hab' | hab' <;> rcases eq_or_lt_of_le hcd with hcd' | hcd'
  · subst hab' hcd'; simp [cdfR]
  · subst hab'
    have hw : 0 < d - c := sub_pos.2 hcd'
    simp only [cdfR, hcd'.ne, and_false, ↓reduceIte]
    rw [show a - c + d - a = d - c by ring, div_self hw.ne']; simp
  · subst hcd'
    have hw : 0 < b - a := sub_pos.2 hab'
    simp only [cdfR, hab'.ne, ↓reduceIte, and_true]
    rw [show b - c + c - a = b - a by ring, div_self hw.ne']; simp
  · rw [cdfR_piece hab' hcd']
    have hw1 : 0 < b - a := sub_pos.2 hab'
    have hw2 : 0 < d - c := sub_pos.2 hcd'
    have hP : 0 < min (b - a) (d - c) := lt_min hw1 hw2
    have hsum : min (b - a) (d - c) + max (b - a) (d - c) = b - c + d - a := by
      rw [min_add_max]; ring
    have h1 : ¬ b - c + d - a ≤ 0 := by linarith
    have h2 : ¬ b - c + d - a ≤ min (b - a) (d - c) := by
      have := max_le_iff.1 (le_refl (max (b - a) (d - c))); linarith [le_max_left (b - a) (d - c)]
    have h3 : ¬ b - c + d - a ≤ max (b - a) (d - c) := by linarith
    simp only [h1, h2, h3, ↓reduceIte, hsum, le_refl, sub_self]
    simp

/-! ## The coordinate difference `Z = X_{o₁} - X_{o₂}` on a box -/

section Diff

variable {m : ℕ} {lo hi : Fin m → ℝ}

/-- the distribution function of `X_{o₁} - X_{o₂}` -/
def cdfO (lo hi : Fin m → ℝ) (o₁ o₂ : Option ℕ) (z : ℝ) : ℝ :=
  cdfR (oget lo o₁) (oget hi o₁) (oget lo o₂) (oget hi o₂) z

lemma measurable_odiff (o₁ o₂ : Option ℕ) : Measurable fun x : Fin m → ℝ => oget x o₁ - oget x o₂ :=
  (measurable_oget o₁).sub (measurable_oget o₂)

lemma cdfO_mem01 (h : ∀ d, lo d < hi d) (o₁ o₂ : Option ℕ) (z : ℝ) :
    0 ≤ cdfO lo hi o₁ o₂ z ∧ cdfO lo hi o₁ o₂ z ≤ 1 :=
  cdfR_mem01 (oget_le h o₁) (oget_le h o₂) z

lemma cdfO_mono (h : ∀ d, lo d < hi d) {o₁ o₂ : Option ℕ} (ho : ∀ d, o₁ = some d → o₂ ≠ some d)
    {s t : ℝ} (hst : s ≤ t) : cdfO lo hi o₁ o₂ s ≤ cdfO lo hi o₁ o₂ t := by
  have h1 := unifBox_sub_le h ho s
  have h2 := unifBox_sub_le h ho t
  have hm : unifBox lo hi {x | oget x o₁ - oget x o₂ ≤ s} ≤ unifBox lo hi {x | oget x o₁ - oget x o₂ ≤ t} :=
    measure_mono fun x (hx : _ ≤ s) => (hx.trans hst : _ ≤ t)
  rw [h1, h2] at hm
  exact (ENNReal.ofReal_le_ofReal_iff (cdfO_mem01 h o₁ o₂ t).1).1 hm

lemma unifBox_odiff_Ioc (h : ∀ d, lo d < hi d) {o₁ o₂ : Option ℕ} (ho : ∀ d, o₁ = some d → o₂ ≠ some d)
    {s t : ℝ} (hst : s ≤ t) :
    unifBox lo hi {x | oget x o₁ - oget x o₂ ∈ Ioc s t} =
      ENNReal.ofReal (cdfO lo hi o₁ o₂ t - cdfO lo hi o₁ o₂ s) := by
  have hP := unifBox_isProb h
  have e : {x : Fin m → ℝ | oget x o₁ - oget x o₂ ∈ Ioc s t} =
      {x | oget x o₁ - oget x o₂ ≤ t} \ {x | oget x o₁ - oget x o₂ ≤ s} := by
    ext x; simp only [mem_ofPred_eq, mem_Ioc, mem_sdiff, not_le]; tauto
  have hsub : {x : Fin m → ℝ | oget x o₁ - oget x o₂ ≤ s} ⊆ {x | oget x o₁ - oget x o₂ ≤ t} :=
    fun x (hx : _ ≤ s) => (hx.trans hst : _ ≤ t)
  rw [e, measure_sdiff hsub (measurableSet_le (measurable_odiff o₁ o₂) measurable_const).nullMeasurableSet
    (measure_ne_top _ _), unifBox_sub_le h ho, unifBox_sub_le h ho]
  exact (ENNReal.ofReal_sub _ (cdfO_mem01 h o₁ o₂ s).1).symm

lemma unifBox_odiff_Icc (h : ∀ d, lo d < hi d) {o₁ o₂ : Option ℕ} (ho : ∀ d, o₁ = some d → o₂ ≠ some d)
    (hnd : oget lo o₁ < oget hi o₁ ∨ oget lo o₂ < oget hi o₂) {s t : ℝ} (hst : s ≤ t) :
    unifBox lo hi {x | oget x o₁ - oget x o₂ ∈ Icc s t} =
      ENNReal.ofReal (cdfO lo hi o₁ o₂ t - cdfO lo hi o₁ o₂ s) := by
  have e : {x : Fin m → ℝ | oget x o₁ - oget x o₂ ∈ Icc s t} =
      {x | oget x o₁ - oget x o₂ ∈ Ioc s t} ∪ {x | oget x o₁ - oget x o₂ = s} := by
    ext x; simp only [mem_ofPred_eq, mem_Ioc, mem_Icc, mem_union]
    constructor
    · rintro ⟨h1, h2⟩
      rcases eq_or_lt_of_le h1 with h1 | h1
      · exact Or.inr h1.symm
      · exact Or.inl ⟨h1, h2⟩
    · rintro (⟨h1, h2⟩ | h1)
      · exact ⟨h1.le, h2⟩
      · exact ⟨h1.ge, h1 ▸ hst⟩
  rw [e]
  refine le_antisymm ?_ ?_
  · refine (measure_union_le _ _).trans ?_
    rw [unifBox_sub_eq h ho hnd s, add_zero, unifBox_odiff_Ioc h ho hst]
  · rw [← unifBox_odiff_Ioc h ho hst]
    exact measure_mono subset_union_left

/-- a constant difference: `X_{o₁} - X_{o₂}` is a.s. `c₁ - c₂` if both coordinates are constant -/
lemma unifBox_odiff_const (h : ∀ d, lo d < hi d) {o₁ o₂ : Option ℕ} (ho : ∀ d, o₁ = some d → o₂ ≠ some d)
    (h1 : oget lo o₁ = oget hi o₁) (h2 : oget lo o₂ = oget hi o₂) {S : Set ℝ} (hS : MeasurableSet S) :
    unifBox lo hi {x | oget x o₁ - oget x o₂ ∈ S} = S.indicator 1 (oget lo o₁ - oget lo o₂) := by
  have e : {x : Fin m → ℝ | oget x o₁ - oget x o₂ ∈ S} =
      (fun x => (oget x o₁, oget x o₂)) ⁻¹' {p : ℝ × ℝ | p.1 - p.2 ∈ S} := rfl
  have hm : MeasurableSet {p : ℝ × ℝ | p.1 - p.2 ∈ S} := (measurable_fst.sub measurable_snd) hS
  rw [e, ← Measure.map_apply (measurable_oget_pair o₁ o₂) hm, map_oget_pair h ho, ← h1, ← h2,
    uLaw_of_eq, uLaw_of_eq, Measure.dirac_prod_dirac, Measure.dirac_apply' _ hm]
  simp only [Set.indicator, mem_ofPred_eq, Pi.one_apply]

end Diff

/-! ## Fixed-point facts for the strips -/

lemma fx_natAbs (n : ℤ) : fx ((n.natAbs : ℕ) : ℤ) = |fx n| := by
  rw [Int.natCast_natAbs]; unfold fx; push_cast; rw [abs_div, abs_of_pos SC_pos]

lemma fx_ONE : fx ONE = 1 := by unfold fx; rw [ONE_cast]; exact div_self SC_pos.ne'

lemma fx_neg (a : ℤ) : fx (-a) = -fx a := by unfold fx; push_cast; ring

lemma fx_stripAmax (x0 x1 : ℤ) : fx ((stripAmax x0 x1 : ℕ) : ℤ) = max |fx x0| |fx x1| := by
  unfold stripAmax; rw [Nat.cast_max, fx_maxC, fx_natAbs, fx_natAbs]

lemma abs_le_stripAmax {x0 x1 : ℤ} {z : ℝ} (hz : z ∈ Ioc (fx x0) (fx x1)) :
    |z| ≤ fx ((stripAmax x0 x1 : ℕ) : ℤ) := by
  rw [fx_stripAmax]
  rcases le_total 0 z with h | h
  · rw [abs_of_nonneg h]; exact hz.2.trans ((le_abs_self _).trans (le_max_right _ _))
  · rw [abs_of_nonpos h]
    exact (le_trans (by linarith [hz.1]) (neg_le_abs (fx x0))).trans (le_max_left _ _)

lemma stripAmin_le_abs {x0 x1 : ℤ} {z : ℝ} (hz : z ∈ Ioc (fx x0) (fx x1)) :
    fx ((stripAmin x0 x1 : ℕ) : ℤ) ≤ |z| := by
  unfold stripAmin
  split_ifs with h
  · simp [fx_zeroC]
  · rw [Nat.cast_min, fx_min, fx_natAbs, fx_natAbs]
    push Not at h
    rcases le_or_gt x0 0 with h0 | h0
    · have h1 := h h0
      have hz' : z ≤ fx x1 := hz.2
      have hx1 : fx x1 < 0 := by rw [← fx_zeroC]; exact fx_lt_iff.2 h1
      rw [abs_of_neg hx1, abs_of_neg (hz'.trans_lt hx1)]
      exact (min_le_right _ _).trans (by linarith)
    · have hx0 : 0 < fx x0 := fx_pos_iff.2 h0
      rw [abs_of_pos hx0, abs_of_pos (hx0.trans hz.1)]
      exact (min_le_left _ _).trans hz.1.le

lemma stripYbIn_le (x0 x1 : ℤ) :
    fx (stripYbIn x0 x1) ≤ √(1 - fx ((stripAmax x0 x1 : ℕ) : ℤ) ^ 2) :=
  ivMem_lo_le (Iv.mem_sqrt (Iv.mem_sub mem_one (Iv.mem_sqr (Iv.mem_pt _))))

lemma le_stripYbOut (x0 x1 : ℤ) :
    √(1 - fx ((stripAmin x0 x1 : ℕ) : ℤ) ^ 2) ≤ fx (stripYbOut x0 x1) :=
  ivMem_hi_le (Iv.mem_sqrt (Iv.mem_sub mem_one (Iv.mem_sqr (Iv.mem_pt _))))

lemma stripX_zero (P Q : PtBox) : stripX P Q 0 = P.xl - Q.xh := by simp [stripX]

lemma stripX_eight (P Q : PtBox) : stripX P Q 8 = P.xh - Q.xl := by
  unfold stripX
  push_cast
  rw [Int.mul_ediv_cancel _ (by norm_num : (8 : ℤ) ≠ 0)]
  ring

lemma stripX_mono (P Q : PtBox) (hw : 0 ≤ (P.xh - Q.xl) - (P.xl - Q.xh)) {t t' : ℕ} (htt : t ≤ t') :
    stripX P Q t ≤ stripX P Q t' := by
  unfold stripX
  have : ((P.xh - Q.xl) - (P.xl - Q.xh)) * (t : ℤ) ≤ ((P.xh - Q.xl) - (P.xl - Q.xh)) * (t' : ℤ) :=
    mul_le_mul_of_nonneg_left (by exact_mod_cast htt) hw
  have := Int.ediv_le_ediv (by norm_num : (0 : ℤ) < 8) this
  linarith

/-- a point of `(X 0, X n]` lies in one of the strips `(X t, X (t+1)]`, `t < n` -/
lemma exists_strip (X : ℕ → ℝ) {z : ℝ} : ∀ n : ℕ, X 0 < z → z ≤ X n → ∃ t < n, z ∈ Ioc (X t) (X (t + 1))
  | 0, h0, hn => absurd h0 (not_lt.2 hn)
  | n + 1, h0, hn => by
    by_cases h : z ≤ X n
    · obtain ⟨t, ht, hz⟩ := exists_strip X n h0 h
      exact ⟨t, by omega, hz⟩
    · exact ⟨n, by omega, ⟨not_le.1 h, hn⟩⟩

/-- the geometry of an inner strip rectangle -/
lemma sq_add_sq_le_one_of_strip {zx zy : ℝ} {A yb : ℝ}
    (hA : |zx| ≤ A) (hA0 : 0 ≤ A) (hA1 : A < 1) (hzy : |zy| ≤ yb) (hyb : yb ≤ √(1 - A ^ 2)) :
    zx ^ 2 + zy ^ 2 ≤ 1 := by
  have h1 : zx ^ 2 ≤ A ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hA 2
  have h2 : zy ^ 2 ≤ yb ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hzy 2
  have h3 : yb ^ 2 ≤ 1 - A ^ 2 := by
    have hy0 : 0 ≤ yb := (abs_nonneg _).trans hzy
    calc yb ^ 2 ≤ √(1 - A ^ 2) ^ 2 := pow_le_pow_left₀ hy0 hyb 2
      _ = 1 - A ^ 2 := Real.sq_sqrt (by nlinarith)
  linarith

/-! ## The rectangles of the points in fixed point -/

lemma ptBox_fx {k : ℕ} (lo hi : List ℤ) (j : Fin k) :
    fx ((ptBoxes k lo hi).getD j.val default).xl = oget (loR (mDim k) lo) (pc1 j.val) ∧
    fx ((ptBoxes k lo hi).getD j.val default).xh = oget (loR (mDim k) hi) (pc1 j.val) ∧
    fx ((ptBoxes k lo hi).getD j.val default).yl = oget (loR (mDim k) lo) (pc2 j.val) ∧
    fx ((ptBoxes k lo hi).getD j.val default).yh = oget (loR (mDim k) hi) (pc2 j.val) := by
  have hj : (ptBoxes k lo hi).getD j.val default =
      if j.val == 0 then ⟨0, 0, 0, 0⟩
      else if j.val == 1 then ⟨listGet lo 0, listGet hi 0, 0, 0⟩
      else ⟨listGet lo (2 * j.val - 3), listGet hi (2 * j.val - 3), listGet lo (2 * j.val - 2),
        listGet hi (2 * j.val - 2)⟩ := by
    simp [ptBoxes, List.getD_eq_getElem?_getD, j.isLt]
  rw [hj]
  have hk := j.isLt
  obtain ⟨n, hn⟩ : ∃ n, j.val = n := ⟨_, rfl⟩
  rw [hn] at hk ⊢
  rcases n with _ | _ | n
  · simp [pc1, pc2, oget, fx_zeroC]
  · have h0 : 0 < mDim k := by unfold mDim; omega
    simp [pc1, pc2, oget, xget, h0, loR, listGet, fx_zeroC]
  · have h1 : 2 * (n + 2) - 3 < mDim k := by unfold mDim; omega
    have h2 : 2 * (n + 2) - 2 < mDim k := by unfold mDim; omega
    simp only [beq_iff_eq, show n + 2 ≠ 0 by omega, show n + 2 ≠ 1 by omega, ↓reduceIte, pc1, pc2]
    simp [oget, xget, h1, h2, loR, listGet]

lemma natAbs_le_toNat_iff {n y : ℤ} (hy : 0 ≤ y) : n.natAbs ≤ y.toNat ↔ |fx n| ≤ fx y := by
  rw [← fx_natAbs, fx_le_iff, ← Int.toNat_of_nonneg hy]
  constructor
  · intro h; exact_mod_cast h
  · intro h; exact_mod_cast h

/-! ## The inner and outer staircase bounds -/

section Bounds

variable {k : ℕ} {lo hi : List ℤ}

/-- the setting of a pair `i < j` of a valid box: coordinate differences and their laws -/
structure PairSetting (k : ℕ) (lo hi : List ℤ) (i j : Fin k) : Prop where
  valid : ValidBox k lo hi
  lt : i < j

lemma pair_facts (hv : ValidBox k lo hi) {i j : Fin k} (hij : i < j) :
    let L := loR (mDim k) lo
    let H := loR (mDim k) hi
    let P := (ptBoxes k lo hi).getD i.val default
    let Q := (ptBoxes k lo hi).getD j.val default
    let Zx := fun x : Fin (mDim k) → ℝ => oget x (pc1 i.val) - oget x (pc1 j.val)
    let Zy := fun x : Fin (mDim k) → ℝ => oget x (pc2 i.val) - oget x (pc2 j.val)
    (∀ x, sqDist (xcfg k x i) (xcfg k x j) = Zx x ^ 2 + Zy x ^ 2) ∧
    IndepFun Zx Zy (unifBox L H) ∧
    (∀ z, cdfX P Q z = cdfO L H (pc1 i.val) (pc1 j.val) z) ∧
    (∀ z, cdfY P Q z = cdfO L H (pc2 i.val) (pc2 j.val) z) := by
  intro L H P Q Zx Zy
  have h := validBox_lt hv
  have hne : i.val ≠ j.val := Fin.val_injective.ne hij.ne
  obtain ⟨hPxl, hPxh, hPyl, hPyh⟩ := ptBox_fx lo hi i
  obtain ⟨hQxl, hQxh, hQyl, hQyh⟩ := ptBox_fx lo hi j
  refine ⟨fun x => ?_, ?_, fun z => ?_, fun z => ?_⟩
  · simp only [sqDist, xcfg_eq, Zx, Zy]
  · have hd : Disjoint (osupp (mDim k) (pc1 i.val) ∪ osupp (mDim k) (pc1 j.val))
        (osupp (mDim k) (pc2 i.val) ∪ osupp (mDim k) (pc2 j.val)) := by
      rw [Finset.disjoint_union_left, Finset.disjoint_union_right, Finset.disjoint_union_right]
      exact ⟨⟨osupp_disjoint (pc12_disjoint _), osupp_disjoint (pc_disjoint _ _ hne true false)⟩,
        ⟨osupp_disjoint (pc_disjoint _ _ hne.symm true false), osupp_disjoint (pc12_disjoint _)⟩⟩
    exact indepFun_of_depOn h hd (measurable_odiff _ _) (measurable_odiff _ _)
      (((depOn_oget _).mono Finset.subset_union_left).comp₂ ((depOn_oget _).mono Finset.subset_union_right)
        (· - ·))
      (((depOn_oget _).mono Finset.subset_union_left).comp₂ ((depOn_oget _).mono Finset.subset_union_right)
        (· - ·))
  · simp only [cdfX, cdfO, P, Q, L, H]; rw [hPxl, hPxh, hQxl, hQxh]
  · simp only [cdfY, cdfO, P, Q, L, H]; rw [hPyl, hPyh, hQyl, hQyh]

lemma Zx_strips_disjoint {m : ℕ} (Zx : (Fin m → ℝ) → ℝ) (X : ℕ → ℤ) (hX : Monotone X) {t t' : ℕ}
    (htt : t ≠ t') :
    Disjoint (Zx ⁻¹' Ioc (fx (X t)) (fx (X (t + 1)))) (Zx ⁻¹' Ioc (fx (X t')) (fx (X (t' + 1)))) := by
  rw [Set.disjoint_left]
  intro x h1 h2
  simp only [mem_preimage, mem_Ioc] at h1 h2
  rcases lt_or_gt_of_ne htt with h | h
  · have : fx (X (t + 1)) ≤ fx (X t') := fx_le_iff.2 (hX (by omega))
    linarith [h1.2, h2.1]
  · have : fx (X (t' + 1)) ≤ fx (X t) := fx_le_iff.2 (hX (by omega))
    linarith [h1.1, h2.2]

set_option linter.constructorNameAsVariable false in
lemma inner_bound (hv : ValidBox k lo hi) {i j : Fin k} (hij : i < j)
    (hw : 0 < ((ptBoxes k lo hi).getD i.val default).xh - ((ptBoxes k lo hi).getD j.val default).xl -
      (((ptBoxes k lo hi).getD i.val default).xl - ((ptBoxes k lo hi).getD j.val default).xh)) :
    ENNReal.ofReal (∑ t ∈ Finset.range 8,
        innerVal ((ptBoxes k lo hi).getD i.val default) ((ptBoxes k lo hi).getD j.val default)
          (stripX ((ptBoxes k lo hi).getD i.val default) ((ptBoxes k lo hi).getD j.val default) t)
          (stripX ((ptBoxes k lo hi).getD i.val default) ((ptBoxes k lo hi).getD j.val default) (t + 1))) ≤
      unifBox (loR (mDim k) lo) (loR (mDim k) hi) {x | sqDist (xcfg k x i) (xcfg k x j) ≤ 1} := by
  set L := loR (mDim k) lo
  set H := loR (mDim k) hi
  set P := (ptBoxes k lo hi).getD i.val default
  set Q := (ptBoxes k lo hi).getD j.val default
  have h := validBox_lt hv
  have hP := unifBox_isProb h
  have hne : i.val ≠ j.val := Fin.val_injective.ne hij.ne
  obtain ⟨hsq, hind, hcX, hcY⟩ := pair_facts hv hij
  set Zx := fun x : Fin (mDim k) → ℝ => oget x (pc1 i.val) - oget x (pc1 j.val) with hZx
  set Zy := fun x : Fin (mDim k) → ℝ => oget x (pc2 i.val) - oget x (pc2 j.val) with hZy
  have hoX : ∀ d, pc1 i.val = some d → pc1 j.val ≠ some d := pc_disjoint _ _ hne true true
  have hoY : ∀ d, pc2 i.val = some d → pc2 j.val ≠ some d := pc_disjoint _ _ hne false false
  set X : ℕ → ℤ := stripX P Q with hXdef
  have hXm : Monotone X := fun t t' htt => stripX_mono P Q hw.le htt
  -- the strip rectangles
  set E : ℕ → Set (Fin (mDim k) → ℝ) := fun t =>
    if (stripAmax (X t) (X (t + 1)) : ℤ) < ONE ∧ 0 < stripYbIn (X t) (X (t + 1)) then
      Zx ⁻¹' Ioc (fx (X t)) (fx (X (t + 1))) ∩
        Zy ⁻¹' Ioc (fx (-stripYbIn (X t) (X (t + 1)))) (fx (stripYbIn (X t) (X (t + 1))))
    else ∅ with hEdef
  have hEm : ∀ t, MeasurableSet (E t) := by
    intro t; simp only [hEdef]; split_ifs
    · exact ((measurable_odiff _ _) measurableSet_Ioc).inter ((measurable_odiff _ _) measurableSet_Ioc)
    · exact MeasurableSet.empty
  have hval0 : ∀ t, 0 ≤ innerVal P Q (X t) (X (t + 1)) := by
    intro t; unfold innerVal; split_ifs with hc
    · refine mul_nonneg (sub_nonneg.2 ?_) (sub_nonneg.2 ?_)
      · rw [hcY, hcY]
        exact cdfO_mono h hoY (by rw [fx_neg]; linarith [fx_pos_iff.2 hc.2])
      · rw [hcX, hcX]; exact cdfO_mono h hoX (fx_le_iff.2 (hXm (Nat.le_succ t)))
    · exact le_rfl
  have hEμ : ∀ t, unifBox L H (E t) = ENNReal.ofReal (innerVal P Q (X t) (X (t + 1))) := by
    intro t
    simp only [hEdef, innerVal]
    split_ifs with hc
    · rw [hind.measure_inter_preimage_eq_mul _ _ measurableSet_Ioc measurableSet_Ioc]
      have hyb : fx (-stripYbIn (X t) (X (t + 1))) ≤ fx (stripYbIn (X t) (X (t + 1))) := by
        rw [fx_neg]; linarith [fx_pos_iff.2 hc.2]
      have e1 := unifBox_odiff_Ioc h hoX (fx_le_iff.2 (hXm (Nat.le_succ t)))
      have e2 := unifBox_odiff_Ioc h hoY hyb
      change unifBox L H {x | Zx x ∈ _} * unifBox L H {x | Zy x ∈ _} = _
      rw [e1, e2, hcX, hcX, hcY, hcY, mul_comm, ← ENNReal.ofReal_mul (sub_nonneg.2 (cdfO_mono h hoY hyb))]
    · simp
  have hEsub : ∀ t, E t ⊆ {x | sqDist (xcfg k x i) (xcfg k x j) ≤ 1} := by
    intro t x hx
    simp only [hEdef] at hx
    split_ifs at hx with hc
    · obtain ⟨h1, h2⟩ := hx
      simp only [mem_preimage, mem_Ioc] at h1 h2
      show sqDist (xcfg k x i) (xcfg k x j) ≤ 1
      rw [hsq x]
      have hA0 : 0 ≤ fx ((stripAmax (X t) (X (t + 1)) : ℕ) : ℤ) := fx_nonneg_iff.2 (Int.natCast_nonneg _)
      have hA1 : fx ((stripAmax (X t) (X (t + 1)) : ℕ) : ℤ) < 1 := by rw [← fx_ONE]; exact fx_lt_iff.2 hc.1
      refine sq_add_sq_le_one_of_strip (abs_le_stripAmax ⟨h1.1, h1.2⟩) hA0 hA1 ?_ (stripYbIn_le _ _)
      rw [fx_neg] at h2
      exact abs_le.2 ⟨h2.1.le, h2.2⟩
    · exact absurd hx (Set.notMem_empty x)
  have hdisj : PairwiseDisjoint (↑(Finset.range 8)) E := by
    intro t _ t' _ htt
    refine Disjoint.mono ?_ ?_ (Zx_strips_disjoint Zx X hXm htt)
    · intro x hx; simp only [hEdef] at hx; split_ifs at hx
      · exact hx.1
      · exact absurd hx (Set.notMem_empty x)
    · intro x hx; simp only [hEdef] at hx; split_ifs at hx
      · exact hx.1
      · exact absurd hx (Set.notMem_empty x)
  calc ENNReal.ofReal (∑ t ∈ Finset.range 8, innerVal P Q (X t) (X (t + 1)))
      = ∑ t ∈ Finset.range 8, ENNReal.ofReal (innerVal P Q (X t) (X (t + 1))) :=
        ENNReal.ofReal_sum_of_nonneg fun t _ => hval0 t
    _ = ∑ t ∈ Finset.range 8, unifBox L H (E t) := by simp_rw [hEμ]
    _ = unifBox L H (⋃ t ∈ Finset.range 8, E t) := (measure_biUnion_finset hdisj fun t _ => hEm t).symm
    _ ≤ unifBox L H {x | sqDist (xcfg k x i) (xcfg k x j) ≤ 1} :=
        measure_mono (Set.iUnion₂_subset fun t _ => hEsub t)

/-- the geometry of an outer strip -/
lemma abs_le_of_sq_add_sq {zx zy a y : ℝ} (ha : a ≤ |zx|) (ha0 : 0 ≤ a) (h : zx ^ 2 + zy ^ 2 ≤ 1)
    (hy : √(1 - a ^ 2) ≤ y) : |zy| ≤ y := by
  have h1 : a ^ 2 ≤ zx ^ 2 := by rw [← sq_abs zx]; exact pow_le_pow_left₀ ha0 ha 2
  have h2 : zy ^ 2 ≤ 1 - a ^ 2 := by linarith
  calc |zy| = √(zy ^ 2) := (Real.sqrt_sq_eq_abs zy).symm
    _ ≤ √(1 - a ^ 2) := Real.sqrt_le_sqrt h2
    _ ≤ y := hy

lemma eq_one_or_neg_one_of {zx zy a : ℝ} (ha : a ≤ |zx|) (ha1 : 1 ≤ a) (h : zx ^ 2 + zy ^ 2 ≤ 1) :
    zx = 1 ∨ zx = -1 := by
  have h1 : |zx| ≤ 1 := by
    rw [← sq_le_one_iff_abs_le_one]; nlinarith [sq_nonneg zy]
  have h2 : |zx| = 1 := le_antisymm h1 (ha1.trans ha)
  rcases abs_eq (zero_le_one) |>.1 h2 with h3 | h3
  · exact Or.inl h3
  · exact Or.inr h3

set_option linter.constructorNameAsVariable false in
lemma outer_bound (hv : ValidBox k lo hi) {i j : Fin k} (hij : i < j)
    (hw : 0 < ((ptBoxes k lo hi).getD i.val default).xh - ((ptBoxes k lo hi).getD j.val default).xl -
      (((ptBoxes k lo hi).getD i.val default).xl - ((ptBoxes k lo hi).getD j.val default).xh)) :
    unifBox (loR (mDim k) lo) (loR (mDim k) hi) {x | sqDist (xcfg k x i) (xcfg k x j) ≤ 1} ≤
      ENNReal.ofReal (∑ t ∈ Finset.range 8,
        outerVal ((ptBoxes k lo hi).getD i.val default) ((ptBoxes k lo hi).getD j.val default)
          (stripX ((ptBoxes k lo hi).getD i.val default) ((ptBoxes k lo hi).getD j.val default) t)
          (stripX ((ptBoxes k lo hi).getD i.val default) ((ptBoxes k lo hi).getD j.val default) (t + 1))) := by
  have h := validBox_lt hv
  have hne : i.val ≠ j.val := Fin.val_injective.ne hij.ne
  obtain ⟨hsq, hind, hcX, hcY⟩ := pair_facts hv hij
  obtain ⟨hPxl, hPxh, hPyl, hPyh⟩ := ptBox_fx lo hi i
  obtain ⟨hQxl, hQxh, hQyl, hQyh⟩ := ptBox_fx lo hi j
  obtain ⟨hPx, hPy⟩ := ptBoxes_ordered hv i
  obtain ⟨hQx, hQy⟩ := ptBoxes_ordered hv j
  set L := loR (mDim k) lo
  set H := loR (mDim k) hi
  set P := (ptBoxes k lo hi).getD i.val default
  set Q := (ptBoxes k lo hi).getD j.val default
  have hP := unifBox_isProb h
  set Zx := fun x : Fin (mDim k) → ℝ => oget x (pc1 i.val) - oget x (pc1 j.val) with hZx
  set Zy := fun x : Fin (mDim k) → ℝ => oget x (pc2 i.val) - oget x (pc2 j.val) with hZy
  have hoX : ∀ d, pc1 i.val = some d → pc1 j.val ≠ some d := pc_disjoint _ _ hne true true
  have hoY : ∀ d, pc2 i.val = some d → pc2 j.val ≠ some d := pc_disjoint _ _ hne false false
  set X : ℕ → ℤ := stripX P Q with hXdef
  have hXm : Monotone X := fun t t' htt => stripX_mono P Q hw.le htt
  have hndXR : fx P.xl < fx P.xh ∨ fx Q.xl < fx Q.xh := by rw [fx_lt_iff, fx_lt_iff]; omega
  have hndX : oget L (pc1 i.val) < oget H (pc1 i.val) ∨ oget L (pc1 j.val) < oget H (pc1 j.val) := by
    rw [← hPxl, ← hPxh, ← hQxl, ← hQxh]; exact hndXR
  have hcXR : ∀ z, cdfO L H (pc1 i.val) (pc1 j.val) z = cdfR (fx P.xl) (fx P.xh) (fx Q.xl) (fx Q.xh) z := by
    intro z; rw [← hcX]; rfl
  -- the two ends
  set D := {x : Fin (mDim k) → ℝ | sqDist (xcfg k x i) (xcfg k x j) ≤ 1} with hDdef
  set A := {x : Fin (mDim k) → ℝ | Zx x ≤ fx (X 0)} with hAdef
  set C := {x : Fin (mDim k) → ℝ | Zx x ≤ fx (X 8)}ᶜ with hCdef
  set B : ℕ → Set (Fin (mDim k) → ℝ) := fun t => Zx ⁻¹' Ioc (fx (X t)) (fx (X (t + 1))) ∩ D with hBdef
  have hμA : unifBox L H A = 0 := by
    have := unifBox_sub_le h hoX (fx (X 0))
    change unifBox L H {x | oget x (pc1 i.val) - oget x (pc1 j.val) ≤ fx (X 0)} = 0
    rw [this]
    change ENNReal.ofReal (cdfO L H (pc1 i.val) (pc1 j.val) (fx (X 0))) = 0
    rw [hcXR, hXdef, stripX_zero, fx_subC, cdfR_left (fx_le_iff.2 hPx) (fx_le_iff.2 hQx) hndXR,
      ENNReal.ofReal_zero]
  have hμC : unifBox L H C = 0 := by
    rw [hCdef, prob_compl_eq_one_sub (measurableSet_le (measurable_odiff _ _) measurable_const)]
    have := unifBox_sub_le h hoX (fx (X 8))
    change 1 - unifBox L H {x | oget x (pc1 i.val) - oget x (pc1 j.val) ≤ fx (X 8)} = 0
    rw [this]
    change 1 - ENNReal.ofReal (cdfO L H (pc1 i.val) (pc1 j.val) (fx (X 8))) = 0
    rw [hcXR, hXdef, stripX_eight, fx_subC, cdfR_right (fx_le_iff.2 hPx) (fx_le_iff.2 hQx),
      ENNReal.ofReal_one, tsub_self]
  have hcover : D ⊆ A ∪ (⋃ t ∈ Finset.range 8, B t) ∪ C := by
    intro x hx
    by_cases hA : Zx x ≤ fx (X 0)
    · exact Or.inl (Or.inl hA)
    by_cases hC : Zx x ≤ fx (X 8)
    · obtain ⟨t, ht, hz⟩ := exists_strip (fun t => fx (X t)) 8 (not_le.1 hA) hC
      exact Or.inl (Or.inr (Set.mem_biUnion (Finset.mem_range.2 ht) ⟨hz, hx⟩))
    · exact Or.inr hC
  -- each strip
  have hB : ∀ t, unifBox L H (B t) ≤ ENNReal.ofReal (outerVal P Q (X t) (X (t + 1))) := by
    intro t
    have hXt : fx (X t) ≤ fx (X (t + 1)) := fx_le_iff.2 (hXm (Nat.le_succ t))
    have hIoc := unifBox_odiff_Ioc h hoX hXt
    unfold outerVal
    set y := stripYbOut (X t) (X (t + 1)) with hydef
    have hy0 : 0 ≤ fx y := (Real.sqrt_nonneg _).trans (le_stripYbOut _ _)
    by_cases hamin : ((stripAmin (X t) (X (t + 1)) : ℕ) : ℤ) < ONE
    · simp only [hamin, ↓reduceIte]
      have hgeo : ∀ x ∈ B t, |Zy x| ≤ fx y := by
        intro x ⟨hx1, hx2⟩
        refine abs_le_of_sq_add_sq (stripAmin_le_abs hx1) (fx_nonneg_iff.2 (Int.natCast_nonneg _)) ?_
          (le_stripYbOut _ _)
        rw [← hsq x]; exact hx2
      have hsub : B t ⊆ Zx ⁻¹' Ioc (fx (X t)) (fx (X (t + 1))) ∩ Zy ⁻¹' Icc (fx (-y)) (fx y) := by
        intro x hx
        refine ⟨hx.1, ?_⟩
        rw [fx_neg]; exact abs_le.1 (hgeo x hx)
      refine (measure_mono hsub).trans ?_
      rw [hind.measure_inter_preimage_eq_mul _ _ measurableSet_Ioc measurableSet_Icc]
      change unifBox L H {x | Zx x ∈ _} * unifBox L H {x | Zy x ∈ _} ≤ _
      rw [hIoc]
      by_cases hydeg : P.yh = P.yl ∧ Q.yh = Q.yl
      · simp only [hydeg, and_self, ↓reduceIte]
        have h1 : oget L (pc2 i.val) = oget H (pc2 i.val) := by rw [← hPyl, ← hPyh, hydeg.1]
        have h2 : oget L (pc2 j.val) = oget H (pc2 j.val) := by rw [← hQyl, ← hQyh, hydeg.2]
        have hconst := unifBox_odiff_const h hoY h1 h2 (measurableSet_Icc (a := fx (-y)) (b := fx y))
        have hval : oget L (pc2 i.val) - oget L (pc2 j.val) = fx (P.yl - Q.yl) := by
          rw [fx_subC, hPyl, hQyl]
        change _ * unifBox L H {x | oget x (pc2 i.val) - oget x (pc2 j.val) ∈ Icc (fx (-y)) (fx y)} ≤ _
        rw [hconst, hval, hcX, hcX]
        have hiff := natAbs_le_toNat_iff (n := P.yl - Q.yl) (fx_nonneg_iff.1 hy0)
        by_cases hc : (P.yl - Q.yl).natAbs ≤ y.toNat
        · have hm : fx (P.yl - Q.yl) ∈ Icc (fx (-y)) (fx y) := by rw [fx_neg]; exact abs_le.1 (hiff.1 hc)
          simp only [hc, ↓reduceIte, Set.indicator_of_mem hm, Pi.one_apply, mul_one, one_mul]
          exact le_rfl
        · have hm : fx (P.yl - Q.yl) ∉ Icc (fx (-y)) (fx y) := by
            rw [fx_neg]; exact fun hm => hc (hiff.2 (abs_le.2 hm))
          simp only [hc, ↓reduceIte, Set.indicator_of_notMem hm, mul_zero, zero_mul, ENNReal.ofReal_zero]
          exact le_rfl
      · simp only [hydeg, ↓reduceIte]
        have hndY : oget L (pc2 i.val) < oget H (pc2 i.val) ∨ oget L (pc2 j.val) < oget H (pc2 j.val) := by
          rw [← hPyl, ← hPyh, ← hQyl, ← hQyh, fx_lt_iff, fx_lt_iff]
          by_cases hpe : P.yh = P.yl
          · exact Or.inr (lt_of_le_of_ne hQy (fun hq => hydeg ⟨hpe, hq.symm⟩))
          · exact Or.inl (lt_of_le_of_ne hPy (Ne.symm hpe))
        have hyy : fx (-y) ≤ fx y := by rw [fx_neg]; linarith
        have hIcc := unifBox_odiff_Icc h hoY hndY hyy
        change _ * unifBox L H {x | oget x (pc2 i.val) - oget x (pc2 j.val) ∈ Icc (fx (-y)) (fx y)} ≤ _
        rw [hIcc, hcX, hcX, hcY, hcY, mul_comm, ← ENNReal.ofReal_mul (sub_nonneg.2 (cdfO_mono h hoY hyy))]
    · simp only [hamin, ↓reduceIte, ENNReal.ofReal_zero, nonpos_iff_eq_zero]
      have ha1 : 1 ≤ fx ((stripAmin (X t) (X (t + 1)) : ℕ) : ℤ) := by
        rw [← fx_ONE]; exact fx_le_iff.2 (not_lt.1 hamin)
      have hsub : B t ⊆ {x | oget x (pc1 i.val) - oget x (pc1 j.val) = 1} ∪
          {x | oget x (pc1 i.val) - oget x (pc1 j.val) = -1} := by
        intro x ⟨hx1, hx2⟩
        exact eq_one_or_neg_one_of (stripAmin_le_abs hx1) ha1 (by rw [← hsq x]; exact hx2)
      refine le_antisymm ((measure_mono hsub).trans ((measure_union_le _ _).trans ?_)) zero_le
      rw [unifBox_sub_eq h hoX hndX 1, unifBox_sub_eq h hoX hndX (-1), add_zero]
  have hval0 : ∀ t, 0 ≤ outerVal P Q (X t) (X (t + 1)) := by
    intro t
    have hXt : fx (X t) ≤ fx (X (t + 1)) := fx_le_iff.2 (hXm (Nat.le_succ t))
    have hy0 : 0 ≤ fx (stripYbOut (X t) (X (t + 1))) := (Real.sqrt_nonneg _).trans (le_stripYbOut _ _)
    have hXd : 0 ≤ cdfX P Q (fx (X (t + 1))) - cdfX P Q (fx (X t)) :=
      sub_nonneg.2 (by rw [hcX, hcX]; exact cdfO_mono h hoX hXt)
    have hYd : 0 ≤ cdfY P Q (fx (stripYbOut (X t) (X (t + 1)))) -
        cdfY P Q (fx (-stripYbOut (X t) (X (t + 1)))) :=
      sub_nonneg.2 (by rw [hcY, hcY]; exact cdfO_mono h hoY (by rw [fx_neg]; linarith))
    unfold outerVal
    split_ifs
    all_goals first
      | exact le_rfl
      | exact mul_nonneg zero_le_one hXd
      | exact mul_nonneg le_rfl hXd
      | exact mul_nonneg hYd hXd
  calc unifBox L H D ≤ unifBox L H (A ∪ (⋃ t ∈ Finset.range 8, B t) ∪ C) := measure_mono hcover
    _ ≤ unifBox L H A + unifBox L H (⋃ t ∈ Finset.range 8, B t) + unifBox L H C :=
        (measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl)
    _ ≤ 0 + ∑ t ∈ Finset.range 8, unifBox L H (B t) + 0 := by
        rw [hμA, hμC]; exact add_le_add (add_le_add le_rfl (measure_biUnion_finset_le _ _)) le_rfl
    _ ≤ ∑ t ∈ Finset.range 8, ENNReal.ofReal (outerVal P Q (X t) (X (t + 1))) := by
        rw [zero_add, add_zero]; exact Finset.sum_le_sum fun t _ => hB t
    _ = ENNReal.ofReal (∑ t ∈ Finset.range 8, outerVal P Q (X t) (X (t + 1))) :=
        (ENNReal.ofReal_sum_of_nonneg fun t _ => hval0 t).symm

end Bounds

/-! ## `StripRealProp` -/

lemma cdfR_mono {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d) {s t : ℝ} (hst : s ≤ t) :
    cdfR a b c d s ≤ cdfR a b c d t := by
  have hP1 := uLaw_isProb a b
  have hP2 := uLaw_isProb c d
  have hm : ((uLaw a b).prod (uLaw c d)) {p : ℝ × ℝ | p.1 - p.2 ≤ s} ≤
      ((uLaw a b).prod (uLaw c d)) {p : ℝ × ℝ | p.1 - p.2 ≤ t} :=
    measure_mono fun p (hp : _ ≤ s) => (hp.trans hst : _ ≤ t)
  rw [cdf_prod hab hcd, cdf_prod hab hcd, ENNReal.ofReal_le_ofReal_iff (cdfR_mem01 hab hcd t).1] at hm
  exact hm

lemma outerVal_nonneg {P Q : PtBox} (hPx : P.xl ≤ P.xh) (hPy : P.yl ≤ P.yh) (hQx : Q.xl ≤ Q.xh)
    (hQy : Q.yl ≤ Q.yh) {x0 x1 : ℤ} (hx : x0 ≤ x1) : 0 ≤ outerVal P Q x0 x1 := by
  have hXd : 0 ≤ cdfX P Q (fx x1) - cdfX P Q (fx x0) :=
    sub_nonneg.2 (cdfR_mono (fx_le_iff.2 hPx) (fx_le_iff.2 hQx) (fx_le_iff.2 hx))
  have hy0 : 0 ≤ fx (stripYbOut x0 x1) := (Real.sqrt_nonneg _).trans (le_stripYbOut _ _)
  have hYd : 0 ≤ cdfY P Q (fx (stripYbOut x0 x1)) - cdfY P Q (fx (-stripYbOut x0 x1)) :=
    sub_nonneg.2 (cdfR_mono (fx_le_iff.2 hPy) (fx_le_iff.2 hQy) (by rw [fx_neg]; linarith))
  unfold outerVal
  split_ifs
  all_goals first
    | exact le_rfl
    | exact mul_nonneg zero_le_one hXd
    | exact mul_nonneg le_rfl hXd
    | exact mul_nonneg hYd hXd

theorem stripRealProp : StripRealProp := by
  intro k lo hi hv i j hij hw
  have h := validBox_lt hv
  have hP := unifBox_isProb h
  have hin := inner_bound hv hij hw
  have hout := outer_bound hv hij hw
  obtain ⟨hPx, hPy⟩ := ptBoxes_ordered hv i
  obtain ⟨hQx, hQy⟩ := ptBoxes_ordered hv j
  have hVt : volume (rbox (loR (mDim k) lo) (loR (mDim k) hi)) ≠ ⊤ := volume_rbox_ne_top
  have hDm : MeasurableSet {x : Fin (mDim k) → ℝ | sqDist (xcfg k x i) (xcfg k x j) ≤ 1} :=
    measurableSet_le (continuous_pairSq i j).measurable measurable_const
  have hS0 : 0 ≤ ∑ t ∈ Finset.range 8,
      outerVal ((ptBoxes k lo hi).getD i.val default) ((ptBoxes k lo hi).getD j.val default)
        (stripX ((ptBoxes k lo hi).getD i.val default) ((ptBoxes k lo hi).getD j.val default) t)
        (stripX ((ptBoxes k lo hi).getD i.val default) ((ptBoxes k lo hi).getD j.val default) (t + 1)) :=
    Finset.sum_nonneg fun t _ => outerVal_nonneg hPx hPy hQx hQy (stripX_mono _ _ hw.le (Nat.le_succ t))
  constructor
  · rw [sep_eq_inter, volume_boxOf_inter h, volume_boxOf h, ENNReal.ofReal_mul (le_max_right _ _),
      ENNReal.ofReal_toReal hVt, mul_comm, ENNReal.ofReal_max, ENNReal.ofReal_zero, max_eq_left zero_le]
    exact mul_le_mul_right hin _
  · have hcompl : {x : Fin (mDim k) → ℝ | 1 < sqDist (xcfg k x i) (xcfg k x j)} =
        {x | sqDist (xcfg k x i) (xcfg k x j) ≤ 1}ᶜ := by
      ext x; simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, not_le]
    rw [sep_eq_inter, hcompl, volume_boxOf_inter h, volume_boxOf h, prob_compl_eq_one_sub hDm,
      ENNReal.ofReal_mul (le_max_right _ _), ENNReal.ofReal_toReal hVt, mul_comm, ENNReal.ofReal_max,
      ENNReal.ofReal_zero, max_eq_left zero_le, ENNReal.ofReal_sub _ hS0, ENNReal.ofReal_one]
    exact mul_le_mul_right (tsub_le_tsub_left hout _) _

/-- `ProbStripsProp`, given the code part `StripCodeProp` -/
theorem probStripsProp_of_code (hC : StripCodeProp) : ProbStripsProp :=
  probStripsProp_of_strip stripRealProp hC

end BHH
