/-
T3 (`FrangeSound`): `frange` encloses `r² + q² + 2 r q c` over a box, from Lemma 4 over the reals (`quadBox_aux`,
G6) and the interval evaluation of the corner values and edge minima.
-/
import W2.TabIvl
import W2.GeoQuad

open Set Real BHH.Cert

noncomputable section

namespace BHH.W2.TabB

open BHH BHH.W2 W2C

/-- the interval value of `r² + q² + 2 r q c` used by `frange` -/
def fvalB (r q c : Iv) : Iv := Iv.add (Iv.add (Iv.sqr r) (Iv.sqr q)) (Iv.mul2e (Iv.mul (Iv.mul r q) c) 1)

lemma mem_fvalB {ρ κ γ : ℝ} {r q c : Iv} (hr : ivMem ρ r) (hq : ivMem κ q) (hc : ivMem γ c) :
    ivMem (ρ ^ 2 + κ ^ 2 + 2 * ρ * κ * γ) (fvalB r q c) := by
  have := Iv.mem_add (Iv.mem_add (Iv.mem_sqr hr) (Iv.mem_sqr hq)) (Iv.mem_mul2e (Iv.mem_mul (Iv.mem_mul hr hq) hc) 1)
  unfold fvalB
  convert this using 1
  ring

/-- one edge step of `frange`'s lower bound -/
def eStep (cmin oneC2 : Iv) (m : ℤ) (e : Iv × Iv × Iv) : ℤ :=
  if (Iv.neg (Iv.mul cmin e.1)).hi < e.2.1.lo ∨ e.2.2.hi < (Iv.neg (Iv.mul cmin e.1)).lo then m
  else min m (Iv.mul (Iv.sqr e.1) oneC2).lo

lemma eStep_le (cmin oneC2 : Iv) (m : ℤ) (e : Iv × Iv × Iv) : eStep cmin oneC2 m e ≤ m := by
  unfold eStep
  split_ifs
  · exact le_rfl
  · exact min_le_left _ _

lemma eStep_le_val {cmin oneC2 : Iv} (m : ℤ) {e : Iv × Iv × Iv}
    (h : ¬((Iv.neg (Iv.mul cmin e.1)).hi < e.2.1.lo ∨ e.2.2.hi < (Iv.neg (Iv.mul cmin e.1)).lo)) :
    eStep cmin oneC2 m e ≤ (Iv.mul (Iv.sqr e.1) oneC2).lo := by
  unfold eStep
  rw [ite_eq_right_of_eq_false _ _ (eq_false h)]
  exact min_le_right _ _

lemma frange_snd (r1 r2 q1 q2 cmin cmax : Iv) : (frange r1 r2 q1 q2 cmin cmax).2 =
    max (max (max (max (fvalB r1 q1 cmax).hi (fvalB r1 q1 cmax).hi) (fvalB r1 q2 cmax).hi)
      (fvalB r2 q1 cmax).hi) (fvalB r2 q2 cmax).hi := rfl

lemma frange_fst (r1 r2 q1 q2 cmin cmax : Iv) : (frange r1 r2 q1 q2 cmin cmax).1 =
    let F0 := min (min (min (min (fvalB r1 q1 cmin).lo (fvalB r1 q1 cmin).lo) (fvalB r1 q2 cmin).lo)
      (fvalB r2 q1 cmin).lo) (fvalB r2 q2 cmin).lo
    let oneC2 := Iv.sub (Iv.int 1) (Iv.sqr cmin)
    if 0 ≤ cmin.lo then F0
    else eStep cmin oneC2 (eStep cmin oneC2 (eStep cmin oneC2 (eStep cmin oneC2 F0 (r1, q1, q2)) (r2, q1, q2))
      (q1, r1, r2)) (q2, r1, r2) := rfl

/-- T3: `frange` encloses `r² + q² + 2 r q c` over `[ρ1, ρ2] × [κ1, κ2] × [c1, c2]` -/
theorem frange_sound (r1 r2 q1 q2 cmin cmax : Iv) (ρ1 ρ2 κ1 κ2 c1 c2 : ℝ)
    (h1 : ivMem ρ1 r1) (h2 : ivMem ρ2 r2) (h3 : ivMem κ1 q1) (h4 : ivMem κ2 q2) (h5 : ivMem c1 cmin)
    (h6 : ivMem c2 cmax) (hρ1 : 0 ≤ ρ1) (hκ1 : 0 ≤ κ1) (hc1 : -1 ≤ c1) (hc2 : c2 ≤ 1)
    (r q c : ℝ) (hr : ρ1 ≤ r) (hr' : r ≤ ρ2) (hq : κ1 ≤ q) (hq' : q ≤ κ2) (hc : c1 ≤ c) (hc' : c ≤ c2) :
    fx (frange r1 r2 q1 q2 cmin cmax).1 ≤ r ^ 2 + q ^ 2 + 2 * r * q * c ∧
      r ^ 2 + q ^ 2 + 2 * r * q * c ≤ fx (frange r1 r2 q1 q2 cmin cmax).2 := by
  obtain ⟨P1, v, hv, hvle⟩ := quadBox_aux ρ1 ρ2 κ1 κ2 c1 c2 r q c hρ1 hκ1 hc1 hc2 hr hr' hq hq' hc hc'
  constructor
  · -- lower bound: `fmin ≤ v ≤ f r q c`
    refine le_trans ?_ hvle
    have c11 := ivMem_lo_le (mem_fvalB h1 h3 h5)
    have c12 := ivMem_lo_le (mem_fvalB h1 h4 h5)
    have c21 := ivMem_lo_le (mem_fvalB h2 h3 h5)
    have c22 := ivMem_lo_le (mem_fvalB h2 h4 h5)
    rw [frange_fst]
    dsimp only
    set F0 := min (min (min (min (fvalB r1 q1 cmin).lo (fvalB r1 q1 cmin).lo) (fvalB r1 q2 cmin).lo)
      (fvalB r2 q1 cmin).lo) (fvalB r2 q2 cmin).lo with hF0
    set oneC2 := Iv.sub (Iv.int 1) (Iv.sqr cmin) with hone
    -- every path is at most `F0`
    have hle0 : (if 0 ≤ cmin.lo then F0 else eStep cmin oneC2 (eStep cmin oneC2 (eStep cmin oneC2
        (eStep cmin oneC2 F0 (r1, q1, q2)) (r2, q1, q2)) (q1, r1, r2)) (q2, r1, r2)) ≤ F0 := by
      split_ifs
      · exact le_rfl
      · exact ((eStep_le _ _ _ _).trans ((eStep_le _ _ _ _).trans ((eStep_le _ _ _ _).trans (eStep_le _ _ _ _))))
    have hF11 : fx F0 ≤ ρ1 ^ 2 + κ1 ^ 2 + 2 * ρ1 * κ1 * c1 := by
      refine le_trans ?_ c11
      rw [fx_le_iff, hF0]
      exact (min_le_left _ _).trans ((min_le_left _ _).trans ((min_le_left _ _).trans (min_le_left _ _)))
    have hF12 : fx F0 ≤ ρ1 ^ 2 + κ2 ^ 2 + 2 * ρ1 * κ2 * c1 := by
      refine le_trans ?_ c12
      rw [fx_le_iff, hF0]
      exact (min_le_left _ _).trans ((min_le_left _ _).trans (min_le_right _ _))
    have hF21 : fx F0 ≤ ρ2 ^ 2 + κ1 ^ 2 + 2 * ρ2 * κ1 * c1 := by
      refine le_trans ?_ c21
      rw [fx_le_iff, hF0]
      exact (min_le_left _ _).trans (min_le_right _ _)
    have hF22 : fx F0 ≤ ρ2 ^ 2 + κ2 ^ 2 + 2 * ρ2 * κ2 * c1 := by
      refine le_trans ?_ c22
      rw [fx_le_iff, hF0]
      exact min_le_right _ _
    have hone_mem : ivMem (1 - c1 ^ 2) oneC2 := by
      have := Iv.mem_sub (Iv.mem_int 1) (Iv.mem_sqr h5)
      rw [Int.cast_one] at this
      exact this
    rcases hv with rfl | rfl | rfl | rfl | ⟨hneg, hedge⟩
    · exact (fx_le_iff.mpr hle0).trans hF11
    · exact (fx_le_iff.mpr hle0).trans hF12
    · exact (fx_le_iff.mpr hle0).trans hF21
    · exact (fx_le_iff.mpr hle0).trans hF22
    · -- an edge minimum: `cmin.lo < 0`, and the edge is not skipped
      have hlo : ¬(0 ≤ cmin.lo) := by
        intro h0
        have : (0 : ℝ) ≤ fx cmin.lo := by unfold fx; positivity
        linarith [ivMem_lo_le h5]
      rw [ite_eq_right_of_eq_false _ _ (eq_false hlo)]
      rcases hedge with ⟨rfl, hk1, hk2⟩ | ⟨rfl, hk1, hk2⟩
      · have hx : ivMem (-(c1 * ρ1)) (Iv.neg (Iv.mul cmin r1)) := Iv.mem_neg (Iv.mem_mul h5 h1)
        have hin : ¬((Iv.neg (Iv.mul cmin r1)).hi < q1.lo ∨ q2.hi < (Iv.neg (Iv.mul cmin r1)).lo) := by
          rw [not_or, not_lt, not_lt, ← fx_le_iff, ← fx_le_iff]
          constructor
          · linarith [ivMem_lo_le h3, ivMem_hi_le hx]
          · linarith [ivMem_hi_le h4, ivMem_lo_le hx]
        have hval := ivMem_lo_le (Iv.mem_mul (Iv.mem_sqr h1) hone_mem)
        refine le_trans (fx_le_iff.mpr ?_) hval
        exact (eStep_le _ _ _ _).trans ((eStep_le _ _ _ _).trans ((eStep_le _ _ _ _).trans
          (eStep_le_val (e := (r1, q1, q2)) _ hin)))
      · have hx : ivMem (-(c1 * κ1)) (Iv.neg (Iv.mul cmin q1)) := Iv.mem_neg (Iv.mem_mul h5 h3)
        have hin : ¬((Iv.neg (Iv.mul cmin q1)).hi < r1.lo ∨ r2.hi < (Iv.neg (Iv.mul cmin q1)).lo) := by
          rw [not_or, not_lt, not_lt, ← fx_le_iff, ← fx_le_iff]
          constructor
          · linarith [ivMem_lo_le h1, ivMem_hi_le hx]
          · linarith [ivMem_hi_le h2, ivMem_lo_le hx]
        have hval := ivMem_lo_le (Iv.mem_mul (Iv.mem_sqr h3) hone_mem)
        refine le_trans (fx_le_iff.mpr ?_) hval
        exact (eStep_le _ _ _ _).trans (eStep_le_val (e := (q1, r1, r2)) _ hin)
  · -- upper bound: `f r q c ≤ max of the corner values at c2 ≤ fmax`
    refine P1.trans ?_
    have u11 := ivMem_hi_le (mem_fvalB h1 h3 h6)
    have u12 := ivMem_hi_le (mem_fvalB h1 h4 h6)
    have u21 := ivMem_hi_le (mem_fvalB h2 h3 h6)
    have u22 := ivMem_hi_le (mem_fvalB h2 h4 h6)
    rw [frange_snd, fx_max, fx_max, fx_max, fx_max]
    refine max_le (max_le ?_ ?_) (max_le ?_ ?_)
    · exact u11.trans ((le_max_left _ _).trans ((le_max_left _ _).trans ((le_max_left _ _).trans (le_max_left _ _))))
    · exact u12.trans ((le_max_right _ _).trans ((le_max_left _ _).trans (le_max_left _ _)))
    · exact u21.trans ((le_max_right _ _).trans (le_max_left _ _))
    · exact u22.trans (le_max_right _ _)

end BHH.W2.TabB
