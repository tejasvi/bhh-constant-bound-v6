/-
T2 (`AngleSound`, `AngleRange`): the angle data `mkAData`, `mkDData` (for `NT ≤ 2^30`: the angle intervals stay
inside `(-3π/2, 3π/2)` and `[0, π]`), and the range of `cos` of the angle between two cells.
-/
import W2.TabIvl

open Set Real BHH.Cert

noncomputable section

namespace BHH.W2.TabB

open BHH BHH.W2 W2C

/-! ## `dθ` -/

lemma ONE_eq : ONE = 2 ^ PR := by unfold ONE PR; norm_num

lemma shrD_mul_ONE (x : ℤ) : shrD (x * ONE) PR = x := by
  unfold shrD
  rw [Int.shiftRight_eq_div_pow, ONE_eq]
  exact Int.mul_ediv_cancel x (by positivity)

lemma shrU_mul_ONE (x : ℤ) : shrU (x * ONE) PR = x := by
  unfold shrU
  rw [show -(x * ONE) = -x * ONE by ring, ← shrD, shrD_mul_ONE, neg_neg]

lemma mul_int_nonneg {a : Iv} (ha : 0 ≤ a.lo) {k : ℤ} (hk : 0 ≤ k) : Iv.mul a (Iv.int k) = ⟨a.lo * k, a.hi * k⟩ := by
  have hb : 0 ≤ k * ONE := mul_nonneg hk (by unfold ONE; norm_num)
  unfold Iv.mul Iv.int
  simp only [ha, hb, ↓reduceIte]
  rw [show a.lo * (k * ONE) = a.lo * k * ONE by ring, show a.hi * (k * ONE) = a.hi * k * ONE by ring,
    shrD_mul_ONE, shrU_mul_ONE]

lemma mul_int_neg {a : Iv} (ha : 0 ≤ a.lo) {k : ℤ} (hk : k < 0) : Iv.mul a (Iv.int k) = ⟨a.hi * k, a.lo * k⟩ := by
  have hb : k * ONE < 0 := mul_neg_of_neg_of_pos hk (by unfold ONE; norm_num)
  unfold Iv.mul Iv.int
  simp only [ha, not_le.mpr hb, hb.le, ↓reduceIte]
  rw [show a.hi * (k * ONE) = a.hi * k * ONE by ring, show a.lo * (k * ONE) = a.lo * k * ONE by ring,
    shrD_mul_ONE, shrU_mul_ONE]

lemma dth_lo_nonneg (g : W2C.Grid) (hNT : 0 < g.NT) : 0 ≤ (dthIv g).lo := by
  unfold dthIv divD
  exact Int.ediv_nonneg (by unfold piLo; norm_num) (by exact_mod_cast hNT.le)

lemma dth_hi_lt (g : W2C.Grid) (hNT : 0 < g.NT) : ((dthIv g).hi : ℝ) < (piHi : ℝ) / g.NT + 1 := by
  have := divU_lt_add_one piHi (g.NT : ℤ) (by exact_mod_cast hNT)
  unfold dthIv
  simpa using this

lemma piHi_pos : (0 : ℝ) < piHi := by unfold piHi; norm_num

lemma pi_gt_three' : (3 : ℝ) < π := pi_gt_three

/-- `fx e` for `|e| ≤ piHi + 2^31` is less than `4` in absolute value -/
lemma fx_lt_four {e : ℝ} (h : e ≤ (piHi : ℝ) + 2 ^ 31) : e / 2 ^ PR < 4 := by
  rw [div_lt_iff₀ (by positivity)]
  have : (piHi : ℝ) + 2 ^ 31 < 4 * 2 ^ PR := by unfold piHi PR; norm_num
  linarith

/-! ## T2 -/

lemma ang0_mem (g : W2C.Grid) (hNT : 0 < g.NT) : ivMem (π / g.NT / 2) (Iv.div2e (dthIv g) 1) := by
  have := Iv.mem_div2e (mem_dthIv g hNT) 1
  simpa using this

lemma ang0_bounds (g : W2C.Grid) (h2 : 2 ≤ g.NT) :
    -(3 * π / 2) < fx (Iv.div2e (dthIv g) 1).lo ∧ fx (Iv.div2e (dthIv g) 1).hi < 3 * π / 2 := by
  have hNT : 0 < g.NT := by omega
  have hpi := pi_gt_three'
  have hlo := dth_lo_nonneg g hNT
  have hhi := dth_hi_lt g hNT
  have hNTr : (2 : ℝ) ≤ g.NT := by exact_mod_cast h2
  have hph := piHi_pos
  unfold Iv.div2e
  simp only
  constructor
  · have := lt_shrD_add_one (dthIv g).lo 1
    have h0 : (0 : ℝ) ≤ (dthIv g).lo := by exact_mod_cast hlo
    have hS : (1 : ℝ) ≤ 2 ^ PR := one_le_pow₀ (by norm_num)
    rw [pow_one] at this
    unfold fx
    rw [lt_div_iff₀ (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hS (by linarith : (0 : ℝ) ≤ 3 * π / 2)]
  · have := shrU_lt_add_one (dthIv g).hi 1
    have hq : (piHi : ℝ) / g.NT ≤ piHi / 2 := div_le_div_of_nonneg_left hph.le (by norm_num) hNTr
    have hb : ((shrU (dthIv g).hi 1 : ℤ) : ℝ) ≤ (piHi : ℝ) + 2 ^ 31 := by
      rw [pow_one] at this; linarith
    unfold fx
    linarith [fx_lt_four hb]

lemma ang2_mem (g : W2C.Grid) (hNT : 0 < g.NT) (d : ℤ) :
    ivMem ((2 * d + 1) * (π / g.NT) / 2) (Iv.div2e (Iv.mul (dthIv g) (Iv.int (2 * d + 1))) 1) := by
  have := Iv.mem_div2e (Iv.mem_mul (mem_dthIv g hNT) (Iv.mem_int (2 * d + 1))) 1
  convert this using 1
  push_cast
  ring

lemma ang2_bounds (g : W2C.Grid) (h2 : 2 ≤ g.NT) (hNT30 : g.NT ≤ 2 ^ 30) (d : ℤ) (hd : |d| < g.NT) :
    -(3 * π / 2) < fx (Iv.div2e (Iv.mul (dthIv g) (Iv.int (2 * d + 1))) 1).lo ∧
      fx (Iv.div2e (Iv.mul (dthIv g) (Iv.int (2 * d + 1))) 1).hi < 3 * π / 2 := by
  have hNT : 0 < g.NT := by omega
  have hpi := pi_gt_three'
  have hlo := dth_lo_nonneg g hNT
  have hhi := dth_hi_lt g hNT
  have hNTr : (2 : ℝ) ≤ g.NT := by exact_mod_cast h2
  have hNT30r : (g.NT : ℝ) ≤ 2 ^ 30 := by exact_mod_cast hNT30
  have hph := piHi_pos
  have hlo' : (0 : ℝ) ≤ (dthIv g).lo := by exact_mod_cast hlo
  have hdabs := abs_lt.mp hd
  have hk1 : ((2 * d + 1 : ℤ) : ℝ) ≤ 2 * g.NT - 1 := by
    have : 2 * d + 1 ≤ 2 * (g.NT : ℤ) - 1 := by omega
    exact_mod_cast this
  have hk2 : -(2 * (g.NT : ℝ) - 1) ≤ ((2 * d + 1 : ℤ) : ℝ) := by
    have : -(2 * (g.NT : ℤ) - 1) ≤ 2 * d + 1 := by omega
    exact_mod_cast this
  -- `H k ≤ (piHi/NT + 1) (2 NT - 1) ≤ piHi + 2^31` for `0 ≤ k ≤ 2NT - 1` and `dθ.hi = H`
  have hHpos : (0 : ℝ) ≤ (piHi : ℝ) / g.NT + 1 := by positivity
  have key : ((piHi : ℝ) / g.NT + 1) * (2 * g.NT - 1) ≤ 2 * piHi + 2 ^ 31 := by
    have e : ((piHi : ℝ) / g.NT + 1) * (2 * g.NT - 1) = 2 * piHi - piHi / g.NT + 2 * g.NT - 1 := by
      field_simp
      ring
    rw [e]
    have : (0 : ℝ) ≤ piHi / g.NT := by positivity
    linarith
  have h2pow : (0 : ℝ) < 2 ^ PR := by positivity
  rcases le_or_gt 0 (2 * d + 1) with hk | hk
  · rw [mul_int_nonneg hlo hk]
    unfold Iv.div2e
    simp only
    constructor
    · have := lt_shrD_add_one ((dthIv g).lo * (2 * d + 1)) 1
      have hk' : (0 : ℝ) ≤ ((2 * d + 1 : ℤ) : ℝ) := by exact_mod_cast hk
      have hprod : (0 : ℝ) ≤ (((dthIv g).lo * (2 * d + 1) : ℤ) : ℝ) := by
        rw [Int.cast_mul]; exact mul_nonneg hlo' hk'
      have hgt : (-1 : ℝ) < ((shrD ((dthIv g).lo * (2 * d + 1)) 1 : ℤ) : ℝ) := by
        have : (0 : ℝ) ≤ (((dthIv g).lo * (2 * d + 1) : ℤ) : ℝ) / 2 ^ 1 := by positivity
        linarith
      have hS : (1 : ℝ) ≤ 2 ^ PR := one_le_pow₀ (by norm_num)
      unfold fx
      rw [lt_div_iff₀ h2pow]
      nlinarith [mul_le_mul_of_nonneg_left hS (by linarith : (0 : ℝ) ≤ 3 * π / 2)]
    · have := shrU_lt_add_one ((dthIv g).hi * (2 * d + 1)) 1
      have hk' : (0 : ℝ) ≤ ((2 * d + 1 : ℤ) : ℝ) := by exact_mod_cast hk
      have hm : ((dthIv g).hi : ℝ) * ((2 * d + 1 : ℤ) : ℝ) ≤ ((piHi : ℝ) / g.NT + 1) * (2 * g.NT - 1) :=
        mul_le_mul hhi.le hk1 hk' hHpos
      have hb : ((shrU ((dthIv g).hi * (2 * d + 1)) 1 : ℤ) : ℝ) ≤ (piHi : ℝ) + 2 ^ 31 := by
        push_cast at this hm
        rw [pow_one] at this
        linarith
      unfold fx
      linarith [fx_lt_four hb]
  · rw [mul_int_neg hlo hk]
    unfold Iv.div2e
    simp only
    constructor
    · have := lt_shrD_add_one ((dthIv g).hi * (2 * d + 1)) 1
      have hk' : ((2 * d + 1 : ℤ) : ℝ) < 0 := by exact_mod_cast hk
      -- `H k ≥ (piHi/NT + 1) k ≥ -(piHi/NT + 1)(2NT - 1)`
      have hm1 : ((piHi : ℝ) / g.NT + 1) * ((2 * d + 1 : ℤ) : ℝ) ≤ ((dthIv g).hi : ℝ) * ((2 * d + 1 : ℤ) : ℝ) :=
        mul_le_mul_of_nonpos_right hhi.le hk'.le
      have hm2 : -(((piHi : ℝ) / g.NT + 1) * (2 * g.NT - 1)) ≤ ((piHi : ℝ) / g.NT + 1) * ((2 * d + 1 : ℤ) : ℝ) := by
        nlinarith [mul_le_mul_of_nonneg_left hk2 hHpos]
      have hb : -((piHi : ℝ) + 2 ^ 31) ≤ ((shrD ((dthIv g).hi * (2 * d + 1)) 1 : ℤ) : ℝ) := by
        push_cast at this hm1 hm2
        rw [pow_one] at this
        linarith
      have h4 := fx_lt_four (e := -((shrD ((dthIv g).hi * (2 * d + 1)) 1 : ℤ) : ℝ)) (by linarith)
      unfold fx
      rw [neg_div] at h4
      linarith
    · have := shrU_lt_add_one ((dthIv g).lo * (2 * d + 1)) 1
      have hk' : ((2 * d + 1 : ℤ) : ℝ) < 0 := by exact_mod_cast hk
      have hprod : (((dthIv g).lo * (2 * d + 1) : ℤ) : ℝ) ≤ 0 := by
        rw [Int.cast_mul]; exact mul_nonpos_of_nonneg_of_nonpos hlo' hk'.le
      have hlt : ((shrU ((dthIv g).lo * (2 * d + 1)) 1 : ℤ) : ℝ) < 1 := by
        have : (((dthIv g).lo * (2 * d + 1) : ℤ) : ℝ) / 2 ^ 1 ≤ 0 :=
          div_nonpos_of_nonpos_of_nonneg hprod (by positivity)
        linarith
      have hS : (1 : ℝ) ≤ 2 ^ PR := one_le_pow₀ (by norm_num)
      unfold fx
      rw [div_lt_iff₀ h2pow]
      nlinarith [mul_le_mul_of_nonneg_left hS (by linarith : (0 : ℝ) ≤ 3 * π / 2)]

/-- the key bound for `cosK`: `(NT - 1) dθ.hi ≤ π 2^PR` for `NT ≤ 2^30` -/
lemma mulNat_dth_hi (g : W2C.Grid) (h2 : 2 ≤ g.NT) (hNT30 : g.NT ≤ 2 ^ 30) {k : ℕ} (hk : k < g.NT) :
    fx (Iv.mulNat (dthIv g) k).hi ≤ π := by
  have hNT : 0 < g.NT := by omega
  have hhi := dth_hi_lt g hNT
  have hNTr : (2 : ℝ) ≤ g.NT := by exact_mod_cast h2
  have hNT30r : (g.NT : ℝ) ≤ 2 ^ 30 := by exact_mod_cast hNT30
  have hkr : (k : ℝ) ≤ g.NT - 1 := by
    have : k + 1 ≤ g.NT := hk
    have : ((k + 1 : ℕ) : ℝ) ≤ g.NT := by exact_mod_cast this
    push_cast at this; linarith
  have hph := piHi_pos
  have hpl := piLo_le
  unfold fx at hpl ⊢
  unfold Iv.mulNat
  simp only
  rw [div_le_iff₀ (by positivity)] at hpl ⊢
  have hHpos : (0 : ℝ) ≤ (piHi : ℝ) / g.NT + 1 := by positivity
  have hm : (((dthIv g).hi * (k : ℤ) : ℤ) : ℝ) ≤ ((piHi : ℝ) / g.NT + 1) * (g.NT - 1) := by
    push_cast
    rcases le_or_gt ((dthIv g).hi : ℝ) 0 with hneg | hpos
    · nlinarith [mul_nonpos_of_nonpos_of_nonneg hneg (Nat.cast_nonneg (α := ℝ) k)]
    · exact mul_le_mul hhi.le hkr (Nat.cast_nonneg _) hHpos
  have e : ((piHi : ℝ) / g.NT + 1) * (g.NT - 1) = piHi - piHi / g.NT + g.NT - 1 := by
    field_simp
    ring
  have hq : (piHi : ℝ) / 2 ^ 30 ≤ piHi / g.NT := div_le_div_of_nonneg_left hph.le (by positivity) hNT30r
  have hnum : (piHi : ℝ) - piLo + 2 ^ 30 ≤ piHi / 2 ^ 30 := by unfold piHi piLo; norm_num
  linarith

lemma mem_cosK (g : W2C.Grid) (h2 : 2 ≤ g.NT) (hNT30 : g.NT ≤ 2 ^ 30) {k : ℕ} (hk : k ≤ g.NT) :
    ivMem (Real.cos (k * (π / g.NT))) (cosK g k) := by
  have hNT : 0 < g.NT := by omega
  have hNTr : (0 : ℝ) < g.NT := by exact_mod_cast hNT
  unfold cosK
  split_ifs with h0 hN
  · rw [beq_iff_eq] at h0
    subst h0
    have := Iv.mem_int 1
    simpa using this
  · rw [beq_iff_eq] at hN
    subst hN
    have := Iv.mem_int (-1)
    rw [show ((g.NT : ℕ) : ℝ) * (π / g.NT) = π by field_simp, Real.cos_pi]
    simpa using this
  · rw [beq_iff_eq] at h0 hN
    have hk' : k < g.NT := lt_of_le_of_ne hk hN
    have hm := Iv.mem_mulNat (mem_dthIv g hNT) k
    have hlo : 0 ≤ fx (Iv.mulNat (dthIv g) k).lo := by
      unfold Iv.mulNat fx
      have := dth_lo_nonneg g hNT
      positivity
    have := mem_cosIvDec hm hlo (mulNat_dth_hi g h2 hNT30 hk')
    rwa [mul_comm] at this

/-- T2: the angle data, for `2 ≤ NT ≤ 2^30` -/
theorem angleSound_of (g : W2C.Grid) (h2 : 2 ≤ g.NT) (hNT30 : g.NT ≤ 2 ^ 30) :
    ivMem (Real.cos (π / g.NT / 2)) (mkAData g).ch ∧ ivMem (Real.sin (π / g.NT / 2)) (mkAData g).sh ∧
    ∀ d : ℤ, |d| < g.NT →
      ivMem (Real.cos ((2 * d + 1) * (π / g.NT) / 2)) (mkDData g d).cx ∧
      ivMem (Real.sin ((2 * d + 1) * (π / g.NT) / 2)) (mkDData g d).sy ∧
      ivMem (Real.cos ((|d| + 1) * (π / g.NT))) (mkDData g d).cmin ∧
      ivMem (if |d| ≤ 1 then 1 else Real.cos ((|d| - 1) * (π / g.NT))) (mkDData g d).cmax := by
  have hNT : 0 < g.NT := by omega
  have hpi := pi_pos
  obtain ⟨b0l, b0h⟩ := ang0_bounds g h2
  refine ⟨mem_cosIvG (ang0_mem g hNT) (by linarith) (by linarith),
    mem_sinIvG (ang0_mem g hNT) b0l b0h, ?_⟩
  intro d hd
  obtain ⟨b2l, b2h⟩ := ang2_bounds g h2 hNT30 d hd
  have hdn : d.natAbs < g.NT := by
    have := hd; rw [Int.abs_eq_natAbs] at this; exact_mod_cast this
  have hab : ((d.natAbs : ℕ) : ℝ) = |(d : ℝ)| := by rw [Nat.cast_natAbs, Int.cast_abs]
  refine ⟨mem_cosIvG (ang2_mem g hNT d) (by linarith) (by linarith), mem_sinIvG (ang2_mem g hNT d) b2l b2h,
    ?_, ?_⟩
  · have hk : d.natAbs + 1 ≤ g.NT := by omega
    have := mem_cosK g h2 hNT30 hk
    rw [Nat.cast_add, hab, Nat.cast_one] at this
    rw [Int.cast_abs]
    exact this
  · show ivMem _ (if d.natAbs ≤ 1 then Iv.int 1 else cosK g (d.natAbs - 1))
    by_cases h1 : d.natAbs ≤ 1
    · have h1' : |d| ≤ 1 := by rw [Int.abs_eq_natAbs]; exact_mod_cast h1
      simp only [h1', h1, ↓reduceIte]
      have := Iv.mem_int 1
      simpa using this
    · have h1' : ¬|d| ≤ 1 := by rw [Int.abs_eq_natAbs]; exact_mod_cast h1
      simp only [h1', h1, ↓reduceIte]
      have hk : d.natAbs - 1 ≤ g.NT := by omega
      have := mem_cosK g h2 hNT30 hk
      rw [Nat.cast_sub (by omega), hab, Nat.cast_one] at this
      rw [Int.cast_abs]
      exact this

/-- T2: the angle between a point of the closed cell `[0, h]` and one of `[d h, (d+1) h]` -/
theorem angleRange_of (h : ℝ) (d : ℤ) (N : ℕ) (hh : 0 < h) (hN : h * N = π) (hd : |d| < N)
    (φ φ' : ℝ) (h1 : 0 ≤ φ) (h2 : φ ≤ h) (h3 : d * h ≤ φ') (h4 : φ' ≤ (d + 1) * h) :
    Real.cos ((|d| + 1) * h) ≤ Real.cos (φ' - φ) ∧
      Real.cos (φ' - φ) ≤ (if |d| ≤ 1 then 1 else Real.cos ((|d| - 1) * h)) := by
  have hdN : ((|d| : ℤ) : ℝ) + 1 ≤ N := by
    have : |d| + 1 ≤ (N : ℤ) := by omega
    exact_mod_cast this
  have hd1 := le_abs_self d
  have hd2 := neg_abs_le d
  have hd1r : (d : ℝ) ≤ ((|d| : ℤ) : ℝ) := by exact_mod_cast hd1
  have hd2r : -((|d| : ℤ) : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd2
  have habs0 : (0 : ℝ) ≤ ((|d| : ℤ) : ℝ) := by exact_mod_cast abs_nonneg d
  have hπ : ((|d| : ℤ) : ℝ) * h + h ≤ π := by rw [← hN]; nlinarith
  have hδ : |φ' - φ| ≤ (((|d| : ℤ) : ℝ) + 1) * h := by
    rw [abs_le]; constructor <;> nlinarith
  constructor
  · rw [← Real.cos_abs (φ' - φ), Int.cast_abs]
    rw [Int.cast_abs] at hδ hπ habs0
    exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (by nlinarith) hδ
  · split_ifs with hd1'
    · exact Real.cos_le_one _
    · push Not at hd1'
      have hd2' : (2 : ℝ) ≤ ((|d| : ℤ) : ℝ) := by
        have : (2 : ℤ) ≤ |d| := by omega
        exact_mod_cast this
      have hlow : (((|d| : ℤ) : ℝ) - 1) * h ≤ |φ' - φ| := by
        rcases le_or_gt 0 d with hd0 | hd0
        · have : ((|d| : ℤ) : ℝ) = d := by rw [abs_of_nonneg hd0]
          rw [this]
          have : (d - 1) * h ≤ φ' - φ := by nlinarith
          exact this.trans (le_abs_self _)
        · have : ((|d| : ℤ) : ℝ) = -d := by rw [abs_of_neg hd0]; push_cast; ring
          rw [this]
          have : (-(d : ℝ) - 1) * h ≤ -(φ' - φ) := by nlinarith
          exact this.trans (neg_le_abs _)
      rw [← Real.cos_abs (φ' - φ), Int.cast_abs]
      rw [Int.cast_abs] at hlow hδ hπ hd2'
      exact Real.cos_le_cos_of_nonneg_of_le_pi (by nlinarith) (by nlinarith) hlow

end BHH.W2.TabB
