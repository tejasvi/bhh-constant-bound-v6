/-
T1 (`RingSound`): the per-ring data `mkRing` (radii, area, centroid radius, second moment, the Riemann sums of the
mean of `A_1` over the annulus, the flag `r2 ≤ 1`), for `2 ≤ NT ≤ 2^30` and a positive rounded `r2² - r1²`.
The mean `2/(r2² - r1²) ∫ A_1(r) r dr` lies between the Riemann sums of `A_1` at the left and right ends of the
`NSUB` sub-intervals (`A_1` is increasing), with weights `(b² - a²)/(r2² - r1²)`.
-/
import W2.TabAngle
import W2.GeoProps

open Set Real BHH.Cert MeasureTheory

noncomputable section

namespace BHH.W2.TabB

open BHH BHH.W2 W2C

/-! ## the radii -/

lemma rad_nonneg (g : W2C.Grid) (j : ℕ) : 0 ≤ (gR g).rad j := by
  unfold GridR.rad gR
  simp only
  split_ifs <;> positivity

lemma rad_lt (g : W2C.Grid) (h1 : 0 < g.N1) (h2 : 0 < g.N2) (j : ℕ) : (gR g).rad j < (gR g).rad (j + 1) := by
  have h1r : (0 : ℝ) < g.N1 := by exact_mod_cast h1
  have h2r : (0 : ℝ) < g.N2 := by exact_mod_cast h2
  unfold GridR.rad gR
  simp only
  split_ifs with ha hb hb
  · rw [div_lt_div_iff_of_pos_right h1r]; push_cast; linarith
  · have hj : j = g.N1 := by omega
    subst hj
    rw [div_self h1r.ne', show g.N1 + 1 - g.N1 = 1 by omega]
    have : (0 : ℝ) < ((1 : ℕ) : ℝ) / g.N2 := by positivity
    linarith
  · omega
  · rw [show j + 1 - g.N1 = (j - g.N1) + 1 by omega]
    push_cast
    have : ((j - g.N1 : ℕ) : ℝ) / g.N2 < (((j - g.N1 : ℕ) : ℝ) + 1) / g.N2 :=
      div_lt_div_of_pos_right (by linarith) h2r
    linarith

/-! ## the Riemann sums of the mean of `A_1` (real side) -/

/-- the mean of `A_1(|z|)` over the annulus `r1 < |z| < r2` (as `meanA1` of `W2/TabProps.lean`) -/
def meanA1B (r1 r2 : ℝ) : ℝ := 2 / (r2 ^ 2 - r1 ^ 2) * ∫ r in r1..r2, A1c r * r

lemma A1r_mono {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) : A1c x * x ≤ A1c y * y :=
  mul_le_mul (A1c_mono hx (hx.trans hxy) hxy) hxy hx (A1c_nonneg (hx.trans hxy))

lemma A1r_integrable {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable (fun r => A1c r * r) volume a b := by
  apply MonotoneOn.intervalIntegrable
  intro x hx y hy hxy
  rw [uIcc_of_le hab] at hx hy
  exact A1r_mono (ha.trans hx.1) hxy

lemma piece_bounds {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    A1c a * ((b ^ 2 - a ^ 2) / 2) ≤ ∫ r in a..b, A1c r * r ∧
      ∫ r in a..b, A1c r * r ≤ A1c b * ((b ^ 2 - a ^ 2) / 2) := by
  have hint := A1r_integrable ha hab
  have hlin : ∀ c : ℝ, ∫ r in a..b, c * r = c * ((b ^ 2 - a ^ 2) / 2) := fun c => by
    rw [intervalIntegral.integral_const_mul, integral_id]
  have hc : ∀ c : ℝ, IntervalIntegrable (fun r => c * r) volume a b :=
    fun c => (continuous_const.mul continuous_id).intervalIntegrable a b
  constructor
  · rw [← hlin]
    exact intervalIntegral.integral_mono_on hab (hc _) hint fun x hx =>
      mul_le_mul_of_nonneg_right (A1c_mono ha (ha.trans hx.1) hx.1) (ha.trans hx.1)
  · rw [← hlin]
    exact intervalIntegral.integral_mono_on hab hint (hc _) fun x hx =>
      mul_le_mul_of_nonneg_right (A1c_mono (ha.trans hx.1) (ha.trans hab) hx.2) (ha.trans hx.1)

/-- the partition points `r1 + (r2 - r1) l / n` -/
def ptR (r1 r2 : ℝ) (n l : ℕ) : ℝ := r1 + (r2 - r1) * l / n

lemma ptR_mono {r1 r2 : ℝ} (h12 : r1 ≤ r2) {n : ℕ} (hn : 0 < n) (l : ℕ) : ptR r1 r2 n l ≤ ptR r1 r2 n (l + 1) := by
  unfold ptR
  have : (0 : ℝ) < n := by exact_mod_cast hn
  push_cast
  have : (r2 - r1) * l / n ≤ (r2 - r1) * (l + 1) / n :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) (by linarith)) this.le
  linarith

lemma ptR_nonneg {r1 r2 : ℝ} (h0 : 0 ≤ r1) (h12 : r1 ≤ r2) (n l : ℕ) : 0 ≤ ptR r1 r2 n l := by
  unfold ptR
  have : 0 ≤ (r2 - r1) * l / n := by
    apply div_nonneg (mul_nonneg (by linarith) (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
  linarith

lemma meanA1_riemann {r1 r2 : ℝ} (h0 : 0 ≤ r1) (h12 : r1 < r2) {n : ℕ} (hn : 0 < n) :
    ∑ l ∈ Finset.range n, (ptR r1 r2 n (l + 1) ^ 2 - ptR r1 r2 n l ^ 2) / (r2 ^ 2 - r1 ^ 2) * A1c (ptR r1 r2 n l) ≤
        meanA1B r1 r2 ∧
      meanA1B r1 r2 ≤ ∑ l ∈ Finset.range n,
        (ptR r1 r2 n (l + 1) ^ 2 - ptR r1 r2 n l ^ 2) / (r2 ^ 2 - r1 ^ 2) * A1c (ptR r1 r2 n (l + 1)) := by
  have hD : 0 < r2 ^ 2 - r1 ^ 2 := by nlinarith
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hA0 : ptR r1 r2 n 0 = r1 := by unfold ptR; simp
  have hAn : ptR r1 r2 n n = r2 := by unfold ptR; field_simp; ring
  have hint : ∀ k < n, IntervalIntegrable (fun r => A1c r * r) volume (ptR r1 r2 n k) (ptR r1 r2 n (k + 1)) :=
    fun k _ => A1r_integrable (ptR_nonneg h0 h12.le n k) (ptR_mono h12.le hn k)
  have hsum := intervalIntegral.sum_integral_adjacent_intervals hint
  rw [hA0, hAn] at hsum
  unfold meanA1B
  rw [← hsum, Finset.mul_sum]
  constructor
  · refine Finset.sum_le_sum fun l _ => ?_
    have := (piece_bounds (ptR_nonneg h0 h12.le n l) (ptR_mono h12.le hn l)).1
    have h2 : 0 ≤ 2 / (r2 ^ 2 - r1 ^ 2) := by positivity
    calc (ptR r1 r2 n (l + 1) ^ 2 - ptR r1 r2 n l ^ 2) / (r2 ^ 2 - r1 ^ 2) * A1c (ptR r1 r2 n l)
        = 2 / (r2 ^ 2 - r1 ^ 2) * (A1c (ptR r1 r2 n l) * ((ptR r1 r2 n (l + 1) ^ 2 - ptR r1 r2 n l ^ 2) / 2)) := by
          field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left this h2
  · refine Finset.sum_le_sum fun l _ => ?_
    have := (piece_bounds (ptR_nonneg h0 h12.le n l) (ptR_mono h12.le hn l)).2
    have h2 : 0 ≤ 2 / (r2 ^ 2 - r1 ^ 2) := by positivity
    calc _ ≤ 2 / (r2 ^ 2 - r1 ^ 2) *
          (A1c (ptR r1 r2 n (l + 1)) * ((ptR r1 r2 n (l + 1) ^ 2 - ptR r1 r2 n l ^ 2) / 2)) :=
          mul_le_mul_of_nonneg_left this h2
      _ = (ptR r1 r2 n (l + 1) ^ 2 - ptR r1 r2 n l ^ 2) / (r2 ^ 2 - r1 ^ 2) * A1c (ptR r1 r2 n (l + 1)) := by
          field_simp

/-! ## the interval side -/

/-- the partition point interval of `euRing` -/
def euPt (g : W2C.Grid) (j l : ℕ) : Iv :=
  Iv.add (radIv g j) (Iv.divNat (Iv.mulNat (Iv.sub (radIv g (j + 1)) (radIv g j)) l) g.NSUB)

/-- the rounded `r2² - r1²` -/
def euDen (g : W2C.Grid) (j : ℕ) : Iv := Iv.sub (Iv.sqr (radIv g (j + 1))) (Iv.sqr (radIv g j))

/-- the weight interval of sub-interval `l` -/
def euW (g : W2C.Grid) (j l : ℕ) : Iv :=
  Iv.div (Iv.sub (Iv.sqr (euPt g j (l + 1))) (Iv.sqr (euPt g j l))) (euDen g j)

def euLoT (g : W2C.Grid) (j l : ℕ) : ℤ :=
  shrD (max (euW g j l).lo 0 * max (a1Iv (euPt g j l)).lo 0) PR

def euHiT (g : W2C.Grid) (j l : ℕ) : ℤ :=
  shrU ((euW g j l).hi * (a1Iv (euPt g j (l + 1))).hi) PR

lemma foldl_pair_range (f h : ℕ → ℤ) : ∀ n : ℕ,
    (List.range n).foldl (fun (acc : ℤ × ℤ) l => (acc.1 + f l, acc.2 + h l)) (0, 0) =
      (∑ l ∈ Finset.range n, f l, ∑ l ∈ Finset.range n, h l)
  | 0 => by simp
  | n + 1 => by
    rw [List.range_succ, List.foldl_append, foldl_pair_range f h n]
    simp [Finset.sum_range_succ]

lemma euRing_eq (g : W2C.Grid) (j : ℕ) :
    euRing g j = (∑ l ∈ Finset.range g.NSUB, euLoT g j l, ∑ l ∈ Finset.range g.NSUB, euHiT g j l) :=
  foldl_pair_range (euLoT g j) (euHiT g j) g.NSUB

lemma fx_sum (s : Finset ℕ) (f : ℕ → ℤ) : fx (∑ l ∈ s, f l) = ∑ l ∈ s, fx (f l) := by
  unfold fx
  push_cast
  rw [Finset.sum_div]

section ring
variable (g : W2C.Grid) (h1 : 0 < g.N1) (h2 : 0 < g.N2) (hS : 0 < g.NSUB) (j : ℕ)
include h1 h2 hS

lemma mem_euPt (l : ℕ) : ivMem (ptR ((gR g).rad j) ((gR g).rad (j + 1)) g.NSUB l) (euPt g j l) := by
  have := Iv.mem_add (mem_radIv g h1 h2 j)
    (Iv.mem_divNat (Iv.mem_mulNat (Iv.mem_sub (mem_radIv g h1 h2 (j + 1)) (mem_radIv g h1 h2 j)) l) hS)
  unfold ptR euPt
  exact this

lemma euLoT_le (l : ℕ) :
    fx (euLoT g j l) ≤ (ptR ((gR g).rad j) ((gR g).rad (j + 1)) g.NSUB (l + 1) ^ 2 -
      ptR ((gR g).rad j) ((gR g).rad (j + 1)) g.NSUB l ^ 2) / ((gR g).rad (j + 1) ^ 2 - (gR g).rad j ^ 2) *
        A1c (ptR ((gR g).rad j) ((gR g).rad (j + 1)) g.NSUB l) := by
  set r1 := (gR g).rad j with hr1
  set r2 := (gR g).rad (j + 1) with hr2
  have h0 := rad_nonneg g j
  have h12 := rad_lt g h1 h2 j
  set A := ptR r1 r2 g.NSUB l with hA
  set B := ptR r1 r2 g.NSUB (l + 1) with hB
  have hA0 : 0 ≤ A := ptR_nonneg h0 h12.le _ _
  have hAB : A ≤ B := ptR_mono h12.le hS l
  have hD : 0 < r2 ^ 2 - r1 ^ 2 := by nlinarith
  set w := (B ^ 2 - A ^ 2) / (r2 ^ 2 - r1 ^ 2) with hw
  have hw0 : 0 ≤ w := div_nonneg (by nlinarith) hD.le
  have hSC : (0 : ℝ) < 2 ^ PR := by positivity
  have hc0 : 0 ≤ A1c A := A1c_nonneg hA0
  -- the weight
  have hW : ((max (euW g j l).lo 0 : ℤ) : ℝ) ≤ w * 2 ^ PR := by
    by_cases hden : 0 < (euDen g j).lo
    · have hmem : ivMem w (euW g j l) := by
        unfold euW
        exact Iv.mem_div (Iv.mem_sub (Iv.mem_sqr (mem_euPt g h1 h2 hS j (l + 1)))
          (Iv.mem_sqr (mem_euPt g h1 h2 hS j l)))
          (Iv.mem_sub (Iv.mem_sqr (mem_radIv g h1 h2 (j + 1))) (Iv.mem_sqr (mem_radIv g h1 h2 j))) hden
      rw [Int.cast_max, Int.cast_zero]
      exact max_le hmem.1 (by positivity)
    · have : euW g j l = ⟨-1, 1⟩ := by
        unfold euW Iv.div
        rw [ite_eq_right_of_eq_false _ _ (eq_false hden)]
      rw [this]
      simp only [Int.reduceNeg, Int.cast_max, Int.cast_neg, Int.cast_one, Int.cast_zero]
      exact max_le (by linarith [mul_nonneg hw0 hSC.le]) (by positivity)
  -- the value of `A_1`
  have hU : ((max (a1Iv (euPt g j l)).lo 0 : ℤ) : ℝ) ≤ A1c A * 2 ^ PR := by
    have := (a1Iv_bounds (mem_euPt g h1 h2 hS j l) hA0).1
    unfold fx at this
    rw [div_le_iff₀ hSC] at this
    rw [Int.cast_max, Int.cast_zero]
    exact max_le this (by positivity)
  have hprod : (((max (euW g j l).lo 0 * max (a1Iv (euPt g j l)).lo 0 : ℤ)) : ℝ) ≤ (w * 2 ^ PR) * (A1c A * 2 ^ PR) := by
    rw [Int.cast_mul]
    exact mul_le_mul hW hU (by rw [Int.cast_max, Int.cast_zero]; exact le_max_right _ _) (by positivity)
  have hsh := shrD_le (max (euW g j l).lo 0 * max (a1Iv (euPt g j l)).lo 0) PR
  unfold euLoT fx
  rw [div_le_iff₀ hSC]
  calc ((shrD (max (euW g j l).lo 0 * max (a1Iv (euPt g j l)).lo 0) PR : ℤ) : ℝ)
      ≤ (((max (euW g j l).lo 0 * max (a1Iv (euPt g j l)).lo 0 : ℤ)) : ℝ) / 2 ^ PR := hsh
    _ ≤ (w * 2 ^ PR) * (A1c A * 2 ^ PR) / 2 ^ PR := div_le_div_of_nonneg_right hprod hSC.le
    _ = w * A1c A * 2 ^ PR := by field_simp

lemma euHiT_ge (hden : 0 < (euDen g j).lo) (l : ℕ) :
    (ptR ((gR g).rad j) ((gR g).rad (j + 1)) g.NSUB (l + 1) ^ 2 -
      ptR ((gR g).rad j) ((gR g).rad (j + 1)) g.NSUB l ^ 2) / ((gR g).rad (j + 1) ^ 2 - (gR g).rad j ^ 2) *
        A1c (ptR ((gR g).rad j) ((gR g).rad (j + 1)) g.NSUB (l + 1)) ≤ fx (euHiT g j l) := by
  set r1 := (gR g).rad j with hr1
  set r2 := (gR g).rad (j + 1) with hr2
  have h0 := rad_nonneg g j
  have h12 := rad_lt g h1 h2 j
  set A := ptR r1 r2 g.NSUB l with hA
  set B := ptR r1 r2 g.NSUB (l + 1) with hB
  have hA0 : 0 ≤ A := ptR_nonneg h0 h12.le _ _
  have hB0 : 0 ≤ B := ptR_nonneg h0 h12.le _ _
  have hAB : A ≤ B := ptR_mono h12.le hS l
  have hD : 0 < r2 ^ 2 - r1 ^ 2 := by nlinarith
  set w := (B ^ 2 - A ^ 2) / (r2 ^ 2 - r1 ^ 2) with hw
  have hw0 : 0 ≤ w := div_nonneg (by nlinarith) hD.le
  have hSC : (0 : ℝ) < 2 ^ PR := by positivity
  have hc0 : 0 ≤ A1c B := A1c_nonneg hB0
  have hmem : ivMem w (euW g j l) := by
    unfold euW
    exact Iv.mem_div (Iv.mem_sub (Iv.mem_sqr (mem_euPt g h1 h2 hS j (l + 1)))
      (Iv.mem_sqr (mem_euPt g h1 h2 hS j l)))
      (Iv.mem_sub (Iv.mem_sqr (mem_radIv g h1 h2 (j + 1))) (Iv.mem_sqr (mem_radIv g h1 h2 j))) hden
  have hW : w * 2 ^ PR ≤ ((euW g j l).hi : ℝ) := hmem.2
  have hU : A1c B * 2 ^ PR ≤ ((a1Iv (euPt g j (l + 1))).hi : ℝ) := by
    have := (a1Iv_bounds (mem_euPt g h1 h2 hS j (l + 1)) hB0).2
    unfold fx at this
    rwa [le_div_iff₀ hSC] at this
  have hprod : (w * 2 ^ PR) * (A1c B * 2 ^ PR) ≤ ((((euW g j l).hi * (a1Iv (euPt g j (l + 1))).hi : ℤ)) : ℝ) := by
    rw [Int.cast_mul]
    exact mul_le_mul hW hU (by positivity) (le_trans (by positivity) hW)
  have hsh := le_shrU ((euW g j l).hi * (a1Iv (euPt g j (l + 1))).hi) PR
  unfold euHiT fx
  rw [le_div_iff₀ hSC]
  calc w * A1c B * 2 ^ PR = (w * 2 ^ PR) * (A1c B * 2 ^ PR) / 2 ^ PR := by field_simp
    _ ≤ ((((euW g j l).hi * (a1Iv (euPt g j (l + 1))).hi : ℤ)) : ℝ) / 2 ^ PR :=
        div_le_div_of_nonneg_right hprod hSC.le
    _ ≤ _ := hsh

end ring

lemma half_lo_pos (g : W2C.Grid) (h2 : 2 ≤ g.NT) (hNT30 : g.NT ≤ 2 ^ 30) : 0 < (Iv.div2e (dthIv g) 1).lo := by
  have hNT : 0 < g.NT := by omega
  have hNTr : (0 : ℝ) < g.NT := by exact_mod_cast hNT
  have hNT30r : (g.NT : ℝ) ≤ 2 ^ 30 := by exact_mod_cast hNT30
  have h1 := lt_divD_add_one piLo (g.NT : ℤ) (by exact_mod_cast hNT)
  have h2' := lt_shrD_add_one (divD piLo (g.NT : ℤ)) 1
  have hq : (piLo : ℝ) / 2 ^ 30 ≤ piLo / g.NT :=
    div_le_div_of_nonneg_left (by unfold piLo; norm_num) hNTr hNT30r
  have hnum : (6 : ℝ) < piLo / 2 ^ 30 := by unfold piLo; norm_num
  have : (0 : ℝ) < ((shrD (divD piLo (g.NT : ℤ)) 1 : ℤ) : ℝ) := by
    push_cast at h1
    rw [pow_one] at h2'
    linarith
  unfold Iv.div2e dthIv
  exact_mod_cast this

/-- T1: the per-ring data, when the rounded `r2² - r1²` and `dθ/2` have positive lower ends -/
theorem ringSound_of (g : W2C.Grid) (h1 : 0 < g.N1) (h2 : 0 < g.N2) (hNT : 2 ≤ g.NT)
    (hS : 0 < g.NSUB) (j : ℕ) (hden : 0 < (Iv.sub (Iv.sqr (radIv g (j + 1))) (Iv.sqr (radIv g j))).lo)
    (hhalfpos : 0 < (Iv.div2e (dthIv g) 1).lo) :
    ivMem ((gR g).rad j) (mkRing g j).r1 ∧ ivMem ((gR g).rad (j + 1)) (mkRing g j).r2 ∧
    fx (mkRing g j).areaLo ≤ ((gR g).rad (j + 1) ^ 2 - (gR g).rad j ^ 2) * (π / g.NT) / 2 ∧
    ivMem (secRho ((gR g).rad j) ((gR g).rad (j + 1)) 0 (π / g.NT)) (mkRing g j).rhoc ∧
    ((gR g).rad j ^ 2 + (gR g).rad (j + 1) ^ 2) / 2 - secRho ((gR g).rad j) ((gR g).rad (j + 1)) 0 (π / g.NT) ^ 2
      ≤ fx (mkRing g j).momHi ∧
    fx (mkRing g j).euLo ≤ meanA1B ((gR g).rad j) ((gR g).rad (j + 1)) ∧
    meanA1B ((gR g).rad j) ((gR g).rad (j + 1)) ≤ fx (mkRing g j).euHi ∧
    ((mkRing g j).nflag = true → (gR g).rad (j + 1) ≤ 1) := by
  have hNT0 : 0 < g.NT := by omega
  have hr1 := mem_radIv g h1 h2 j
  have hr2 := mem_radIv g h1 h2 (j + 1)
  have h0 := rad_nonneg g j
  have h12 := rad_lt g h1 h2 j
  have hdth := mem_dthIv g hNT0
  -- the centroid radius
  have hhalf := ang0_mem g hNT0
  obtain ⟨b0l, b0h⟩ := ang0_bounds g hNT
  have hsinc := Iv.mem_div (mem_sinIvG hhalf b0l b0h) hhalf hhalfpos
  have hq := Iv.mem_div (Iv.mem_sub (Iv.mem_mul (Iv.mem_sqr hr2) hr2) (Iv.mem_mul (Iv.mem_sqr hr1) hr1))
    (Iv.mem_sub (Iv.mem_sqr hr2) (Iv.mem_sqr hr1)) hden
  have hrho := Iv.mem_mul (Iv.mem_divNat (Iv.mem_mulNat hq 2) (by norm_num : 0 < 3)) hsinc
  have hrho' : ivMem (secRho ((gR g).rad j) ((gR g).rad (j + 1)) 0 (π / g.NT)) (mkRing g j).rhoc := by
    show ivMem _ (Iv.mul (Iv.divNat (Iv.mulNat (Iv.div (Iv.sub (Iv.mul (Iv.sqr (radIv g (j + 1))) (radIv g (j + 1)))
      (Iv.mul (Iv.sqr (radIv g j)) (radIv g j))) (Iv.sub (Iv.sqr (radIv g (j + 1))) (Iv.sqr (radIv g j)))) 2) 3)
      (Iv.div (sinIvG (Iv.div2e (dthIv g) 1)) (Iv.div2e (dthIv g) 1)))
    convert hrho using 1
    unfold secRho
    rw [sub_zero]
    push_cast
    ring
  refine ⟨hr1, hr2, ?_, hrho', ?_, ?_, ?_, ?_⟩
  · -- the area
    have := Iv.mem_div2e (Iv.mem_mul (Iv.mem_sub (Iv.mem_sqr hr2) (Iv.mem_sqr hr1)) hdth) 1
    have h := ivMem_lo_le this
    rw [pow_one] at h
    exact h
  · -- the second moment
    have hm := Iv.mem_sub (Iv.mem_div2e (Iv.mem_add (Iv.mem_sqr hr1) (Iv.mem_sqr hr2)) 1) (Iv.mem_sqr hrho')
    have h := ivMem_hi_le hm
    rw [pow_one] at h
    show _ ≤ fx (max _ 0)
    rw [fx_max]
    exact le_max_of_le_left h
  · -- the lower Riemann sum
    show fx (euRing g j).1 ≤ _
    rw [euRing_eq, fx_sum]
    exact (Finset.sum_le_sum fun l _ => euLoT_le g h1 h2 hS j l).trans (meanA1_riemann h0 h12 hS).1
  · -- the upper Riemann sum
    show _ ≤ fx (euRing g j).2
    rw [euRing_eq, fx_sum]
    exact (meanA1_riemann h0 h12 hS).2.trans (Finset.sum_le_sum fun l _ => euHiT_ge g h1 h2 hS j hden l)
  · -- the flag `r2 ≤ 1`
    intro hf
    have hj : j + 1 ≤ g.N1 := of_decide_eq_true hf
    have h1r : (0 : ℝ) < g.N1 := by exact_mod_cast h1
    unfold GridR.rad gR
    simp only [hj, ↓reduceIte]
    rw [div_le_one h1r]
    exact_mod_cast hj

end BHH.W2.TabB
