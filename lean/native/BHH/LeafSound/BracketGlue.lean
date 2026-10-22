/-
Module D, part 13: the bracket value of the code (`bracketVal`) is a lower bound of the bracket of module C.
-/
import BHH.LeafSound.BracketK

open BHH.Cert Real MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace BHH

/-- the volume of a valid box as a product of real widths -/
lemma volume_boxOf_prod {k : ℕ} {lo hi : List ℤ} (hv : ValidBox k lo hi) :
    (volume (boxOf lo hi : Set (Fin (mDim k) → ℝ))).toReal = ∏ d, (realLo k hi d - realLo k lo d) := by
  unfold boxOf
  rw [Real.volume_pi_Ico, ENNReal.toReal_prod]
  refine Finset.prod_congr rfl (fun d _ => ?_)
  have := (hv.2.2.1 d.val d.isLt).1
  have : fx (lo.getD d.val 0) ≤ fx (hi.getD d.val 0) := fx_le_iff.mpr this.le
  rw [ENNReal.toReal_ofReal (by linarith)]; rfl

lemma realLo_lt {k : ℕ} {lo hi : List ℤ} (hv : ValidBox k lo hi) (d : Fin (mDim k)) :
    realLo k lo d < realLo k hi d := by
  have h := (hv.2.2.1 d.val d.isLt).1
  show fx (lo.getD d.val 0) < fx (hi.getD d.val 0)
  unfold fx
  have h' : ((lo.getD d.val 0 : ℤ) : ℝ) < ((hi.getD d.val 0 : ℤ) : ℝ) := by exact_mod_cast h
  gcongr

/-- `φ'(t) = -s t^{-s-1}` is increasing on `(0, ∞)` -/
lemma d1_mono {s t1 t2 : ℝ} (hs : 0 < s) (ht1 : 0 < t1) (h : t1 ≤ t2) :
    -s * t1 ^ (-s - 1) ≤ -s * t2 ^ (-s - 1) := by
  have := Real.rpow_le_rpow_of_nonpos ht1 h (by linarith : -s - 1 ≤ 0)
  nlinarith

/-- `φ''(t) = s (s+1) t^{-s-2}` is decreasing on `(0, ∞)` -/
lemma d2_anti {s t1 t2 : ℝ} (hs : 0 < s) (ht1 : 0 < t1) (h : t1 ≤ t2) :
    s * (s + 1) * t2 ^ (-s - 2) ≤ s * (s + 1) * t1 ^ (-s - 2) := by
  have := Real.rpow_le_rpow_of_nonpos ht1 h (by linarith : -s - 2 ≤ 0)
  have : 0 < s * (s + 1) := by positivity
  nlinarith

/-- `φ(t) = t^{-s}` is decreasing on `(0, ∞)` -/
lemma phi_anti {s t1 t2 : ℝ} (hs : 0 < s) (ht1 : 0 < t1) (h : t1 ≤ t2) : phiS s t2 ≤ phiS s t1 := by
  unfold phiS; exact Real.rpow_le_rpow_of_nonpos ht1 h (by linarith)

lemma final_step {v X Y P Q : ℝ} {I : ℝ≥0∞} (hv0 : 0 ≤ v) (hX : X ≤ P) (hY : Y ≤ Q)
    (h : ENNReal.ofReal (v * max P Q) ≤ I) : ENNReal.ofReal (v * max (max X Y) 0) ≤ I := by
  by_cases hpos : max X Y ≤ 0
  · rw [max_eq_right hpos, mul_zero, ENNReal.ofReal_zero]; exact zero_le
  · push_neg at hpos
    rw [max_eq_left hpos.le]
    exact le_trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (max_le_max hX hY) hv0)) h

theorem bracket_glue {k : ℕ} (hk3 : 3 ≤ k) (hBk : BracketPropK k)
    {lo hi : List ℤ} (hv : ValidBox k lo hi) (hlo0 : 0 ≤ listGet lo 0)
    {u : UnionRes} {g : Fin k → Pt} {a : ℝ} (hA : ivMem a u.A)
    (hg : ∀ i : Fin k, ivMem (g i).1 (u.gx.getD i.val default) ∧ ivMem (g i).2 (u.gy.getD i.val default))
    {rr : RemRes} {ρ : (Fin (mDim k) → ℝ) → ℝ} (hρm : Measurable ρ)
    (hρb : ∃ M, ∀ x ∈ rbox (realLo k lo) (realLo k hi), 0 ≤ ρ x ∧ ρ x ≤ M)
    (hρ1 : (∫ x in rbox (realLo k lo) (realLo k hi), ρ x) ≤
      fx (max rr.Er 0) * (volume (rbox (realLo k lo) (realLo k hi))).toReal)
    (hρ2 : (∫ x in rbox (realLo k lo) (realLo k hi), ρ x ^ 2) ≤
      fx (max rr.sEr2 0) ^ 2 * (volume (rbox (realLo k lo) (realLo k hi))).toReal)
    {f : (Fin (mDim k) → ℝ) → ℝ≥0∞}
    (hf : ∀ x ∈ rbox (realLo k lo) (realLo k hi), ENNReal.ofReal (xget x 0 * phiS ((k : ℝ) - 1 / 2)
      (a + ∑ d, gradBox k g d * (x d - (realLo k lo d + realLo k hi d) / 2) + ρ x)) ≤ f x) :
    ENNReal.ofReal ((volume (boxOf lo hi : Set (Fin (mDim k) → ℝ))).toReal *
        fx (bracketVal k (gradList k u) (widthList k lo hi) u.A (sumAbs (gradList k u) (widthList k lo hi))
          (sumSq (gradList k u) (widthList k lo hi)) rr (listGet lo 0) (listGet hi 0))) ≤
      ∫⁻ x in rbox (realLo k lo) (realLo k hi), f x := by
  unfold bracketVal
  dsimp only
  rcases h1 : phiAt k (u.A.hi + max rr.Er 0) with _ | ⟨fa, fa', fa''⟩
  · simp [fx_zero]
  rcases h2 : phiAt k u.A.lo with _ | ⟨g0, f1A, g2⟩
  · simp [fx_zero]
  rcases h3 : phiAt k u.A.hi with _ | ⟨g0', f1Ahi, g2'⟩
  · simp [fx_zero]
  rcases h4 : phiAt k (u.A.lo - sumAbs (gradList k u) (widthList k lo hi)) with _ | ⟨g0'', g1'', f2⟩
  · simp [fx_zero]
  rcases h5 : phiAt k (u.A.lo + max rr.Er 0) with _ | ⟨g05, f1a1, g25⟩
  · simp [fx_zero]
  dsimp only
  split_ifs with htmin
  swap
  · simp [fx_zero]
  -- the real data
  have hm : mDim k = 2 * k - 3 := rfl
  have h0m : 0 < mDim k := by rw [hm]; omega
  set sR : ℝ := (k : ℝ) - 1 / 2 with hsR
  have hs : 0 < sR := by
    have : (3 : ℝ) ≤ k := by exact_mod_cast hk3
    rw [hsR]; linarith
  have hk1 : 1 ≤ k := by omega
  set Rb : ℝ := fx (max rr.Er 0) with hRb_def
  set Sbr : ℝ := fx (max rr.sEr2 0) with hSbr_def
  have hRb : 0 ≤ Rb := fx_nonneg_iff.mpr (le_max_right _ _)
  have hSbr : 0 ≤ Sbr := fx_nonneg_iff.mpr (le_max_right _ _)
  set sumb := sumAbs (gradList k u) (widthList k lo hi) with hsumb
  set Sbc := sumSq (gradList k u) (widthList k lo hi) with hSbc
  set w0 : ℤ := listGet (widthList k lo hi) 0 with hw0
  set h0 : ℝ := fx w0 with hh0
  have hw0e : w0 = listGet hi 0 - listGet lo 0 := by
    rw [hw0]; unfold listGet; rw [widthList_getD k lo hi (by omega)]; rfl
  have hh0e : h0 = xget (realLo k hi) 0 - xget (realLo k lo) 0 := by
    rw [hh0, hw0e, fx_sub, xget_realLo h0m, xget_realLo h0m]; rfl
  have hh0pos : 0 ≤ h0 := by
    rw [hh0e, xget_of_lt _ h0m, xget_of_lt _ h0m]; linarith [realLo_lt hv ⟨0, h0m⟩]
  set b0r : ℝ := gradBox k g ⟨0, h0m⟩ with hb0r
  have hb0 : ivMem b0r ((gradList k u).getD 0 default) := mem_gradList hk3 hg ⟨0, h0m⟩
  have hxb : xget (gradBox k g) 0 = b0r := xget_of_lt _ h0m
  -- the centre of r_2
  have heven : Even (listGet lo 0 + listGet hi 0) := (hv.2.2.1 0 h0m).2
  set rbar : ℝ := xget (fun d => (realLo k lo d + realLo k hi d) / 2) 0 with hrbar
  have hrbar_e : rbar = fx ((listGet lo 0 + listGet hi 0) / 2) := by
    rw [hrbar, xget_of_lt _ h0m, fx_half heven]; rfl
  have hr2c : ivMem rbar (Iv.pt ((listGet lo 0 + listGet hi 0) / 2)) := by rw [hrbar_e]; exact Iv.mem_pt _
  have hrbar0 : 0 ≤ rbar := by
    rw [hrbar, xget_of_lt _ h0m]
    have h1 : 0 ≤ realLo k lo ⟨0, h0m⟩ := fx_nonneg_iff.mpr hlo0
    have h2 := realLo_lt hv ⟨0, h0m⟩
    show 0 ≤ (realLo k lo ⟨0, h0m⟩ + realLo k hi ⟨0, h0m⟩) / 2
    linarith
  -- τ and Sb
  set τ : ℝ := a - ∑ d, |gradBox k g d| * (realLo k hi d - realLo k lo d) / 2 with hτ_def
  have hτ : fx (u.A.lo - sumb) ≤ τ := by
    have h1 := sumAbs_ge hk3 hg lo hi
    have h2 := ivMem_lo_le hA
    rw [fx_sub, hτ_def]; linarith
  have htpos : 0 < fx (u.A.lo - sumb) := by unfold fx; exact div_pos (by exact_mod_cast htmin) (by positivity)
  have hτpos : 0 < τ := lt_of_lt_of_le htpos hτ
  set Sb : ℝ := √(∑ d, (gradBox k g d) ^ 2 * (realLo k hi d - realLo k lo d) ^ 2 / 12) with hSb_def
  have hSb : Sb ≤ √(fx Sbc) := Real.sqrt_le_sqrt (sumSq_ge hk3 hg lo hi)
  have hSb0 : 0 ≤ Sb := Real.sqrt_nonneg _
  -- φ enclosures
  obtain ⟨p1, hfa, hfa', -⟩ := phiAt_sound k hk1 _ _ _ _ h1
  obtain ⟨p2, -, hf1A, -⟩ := phiAt_sound k hk1 _ _ _ _ h2
  obtain ⟨p3, -, hf1Ahi, -⟩ := phiAt_sound k hk1 _ _ _ _ h3
  obtain ⟨p4, -, -, hf2⟩ := phiAt_sound k hk1 _ _ _ _ h4
  obtain ⟨p5, -, hf1a1, -⟩ := phiAt_sound k hk1 _ _ _ _ h5
  have hAlo := ivMem_lo_le hA
  have hAhi := ivMem_hi_le hA
  have hapos : 0 < a := lt_of_lt_of_le p2 hAlo
  have haR : 0 < a + Rb := by linarith
  have hfxAhiE : fx (u.A.hi + max rr.Er 0) = fx u.A.hi + Rb := by rw [hRb_def]; unfold fx; push_cast; ring
  have hfxAloE : fx (u.A.lo + max rr.Er 0) = fx u.A.lo + Rb := by rw [hRb_def]; unfold fx; push_cast; ring
  -- φ'(a) and φ'(a + Rb)
  set d1a : ℝ := -sR * a ^ (-sR - 1) with hd1a
  have hF8 : ivMem d1a ⟨f1A.lo, f1Ahi.hi⟩ := by
    have hP : (0:ℝ) ≤ 2 ^ PR := by positivity
    constructor
    · have h := hf1A.1
      have hm1 : -sR * fx u.A.lo ^ (-sR - 1) ≤ d1a := d1_mono hs p2 hAlo
      show (f1A.lo : ℝ) ≤ d1a * 2 ^ PR
      exact le_trans h (mul_le_mul_of_nonneg_right hm1 hP)
    · have h := hf1Ahi.2
      have hm1 : d1a ≤ -sR * fx u.A.hi ^ (-sR - 1) := d1_mono hs hapos hAhi
      show d1a * 2 ^ PR ≤ (f1Ahi.hi : ℝ)
      exact le_trans (mul_le_mul_of_nonneg_right hm1 hP) h
  set d1aR : ℝ := -sR * (a + Rb) ^ (-sR - 1) with hd1aR
  have hF9 : ivMem d1aR ⟨f1a1.lo, fa'.hi⟩ := by
    have hP : (0:ℝ) ≤ 2 ^ PR := by positivity
    constructor
    · have h := hf1a1.1
      have hle : fx (u.A.lo + max rr.Er 0) ≤ a + Rb := by rw [hfxAloE]; linarith
      have hm1 : -sR * fx (u.A.lo + max rr.Er 0) ^ (-sR - 1) ≤ d1aR := d1_mono hs p5 hle
      show (f1a1.lo : ℝ) ≤ d1aR * 2 ^ PR
      exact le_trans h (mul_le_mul_of_nonneg_right hm1 hP)
    · have h := hfa'.2
      have hle : a + Rb ≤ fx (u.A.hi + max rr.Er 0) := by rw [hfxAhiE]; linarith
      have hm1 : d1aR ≤ -sR * fx (u.A.hi + max rr.Er 0) ^ (-sR - 1) := d1_mono hs haR hle
      show d1aR * 2 ^ PR ≤ (fa'.hi : ℝ)
      exact le_trans (mul_le_mul_of_nonneg_right hm1 hP) h
  -- φ(a + Rb) ≥ fa.lo
  have hF10 : fx fa.lo ≤ phiS sR (a + Rb) := by
    have h := ivMem_lo_le hfa
    have hle : a + Rb ≤ fx (u.A.hi + max rr.Er 0) := by rw [hfxAhiE]; linarith
    have := phi_anti hs haR hle
    unfold phiS at this ⊢; linarith
  -- φ''(τ) ≤ f2.hi
  set d2τ : ℝ := sR * (sR + 1) * τ ^ (-sR - 2) with hd2τ
  have hF11 : d2τ ≤ fx f2.hi := le_trans (d2_anti hs htpos hτ) (ivMem_hi_le hf2)
  have hF11' : 0 ≤ d2τ := by positivity
  have hlo0' : 0 ≤ xget (realLo k lo) 0 := by rw [xget_realLo h0m]; exact fx_nonneg_iff.mpr hlo0
  have hbr := hBk (realLo k lo) (realLo k hi) sR a Rb Sbr (gradBox k g) ρ f (realLo_lt hv) hlo0' hs hRb hSbr
    hρm hρb hρ1 hρ2 hτpos hf
  dsimp only at hbr
  rw [← hh0e, hxb, ← hrbar, ← hd1a, ← hd1aR, ← hd2τ, ← hSb_def] at hbr
  -- the code intervals
  have hw0' : ivMem h0 (Iv.pt w0) := Iv.mem_pt w0
  have ht12 := Iv.mem_divNat (Iv.mem_mul (Iv.mem_mul hb0 hw0') hw0') (by norm_num : 0 < 12)
  have hWI : ivMem ((√(fx Sbc) + Sbr) ^ 2) (((Iv.pt Sbc).sqrt.add (Iv.pt (max rr.sEr2 0))).sqr) :=
    Iv.mem_sqr (Iv.mem_add (Iv.mem_sqrt (Iv.mem_pt Sbc)) (Iv.mem_pt _))
  have hWI' : ivMem ((√(fx Sbc) + √(Sbr ^ 2 + Rb ^ 2)) ^ 2)
      (((Iv.pt Sbc).sqrt.add ((Iv.pt (max rr.sEr2 0)).sqr.add (Iv.pt (max rr.Er 0)).sqr).sqrt).sqr) :=
    Iv.mem_sqr (Iv.mem_add (Iv.mem_sqrt (Iv.mem_pt Sbc))
      (Iv.mem_sqrt (Iv.mem_add (Iv.mem_sqr (Iv.mem_pt _)) (Iv.mem_sqr (Iv.mem_pt _)))))
  have hvB := Iv.mem_sub (Iv.mem_sub (Iv.mem_add (Iv.mem_mul hr2c (Iv.mem_pt fa.lo)) (Iv.mem_mul hF8 ht12))
      (Iv.mem_div2e (Iv.mem_mul (Iv.mem_mul (Iv.mem_abs hF8) hw0') (Iv.mem_pt (max rr.Er 0))) 1))
      (Iv.mem_div2e (Iv.mem_mul (Iv.mem_mul hWI (Iv.mem_pt f2.hi)) hw0') 2)
  have hvA := Iv.mem_sub (Iv.mem_sub (Iv.mem_add (Iv.mem_mul hr2c (Iv.mem_pt fa.lo)) (Iv.mem_mul hF9 ht12))
      (Iv.mem_div2e (Iv.mem_mul (Iv.mem_mul (Iv.mem_abs hF9) hw0') (Iv.mem_pt (max rr.Er 0))) 1))
      (Iv.mem_div2e (Iv.mem_mul (Iv.mem_mul hWI' (Iv.mem_pt f2.hi)) hw0') 2)
  have hvBlo := ivMem_lo_le hvB
  have hvAlo := ivMem_lo_le hvA
  -- real comparisons
  have hf2nn : 0 ≤ fx f2.hi := le_trans hF11' hF11
  have hh04 : 0 ≤ h0 / 4 := div_nonneg hh0pos (by norm_num)
  have e1 : rbar * fx fa.lo ≤ rbar * phiS sR (a + Rb) := mul_le_mul_of_nonneg_left hF10 hrbar0
  have e2 : h0 / 4 * d2τ * (Sb + Sbr) ^ 2 ≤ (√(fx Sbc) + Sbr) ^ 2 * fx f2.hi * h0 / 2 ^ 2 := by
    have q1 : (Sb + Sbr) ^ 2 ≤ (√(fx Sbc) + Sbr) ^ 2 :=
      sq_le_sq' (by linarith only [hSb, hSb0, hSbr]) (by linarith only [hSb])
    calc h0 / 4 * d2τ * (Sb + Sbr) ^ 2 ≤ h0 / 4 * fx f2.hi * (√(fx Sbc) + Sbr) ^ 2 :=
          mul_le_mul (mul_le_mul_of_nonneg_left hF11 hh04) q1 (sq_nonneg _) (mul_nonneg hh04 hf2nn)
      _ = _ := by ring
  have e2' : h0 / 4 * d2τ * (Sb + √(Sbr ^ 2 + Rb ^ 2)) ^ 2 ≤
      (√(fx Sbc) + √(Sbr ^ 2 + Rb ^ 2)) ^ 2 * fx f2.hi * h0 / 2 ^ 2 := by
    have hq := Real.sqrt_nonneg (Sbr ^ 2 + Rb ^ 2)
    have q1 : (Sb + √(Sbr ^ 2 + Rb ^ 2)) ^ 2 ≤ (√(fx Sbc) + √(Sbr ^ 2 + Rb ^ 2)) ^ 2 :=
      sq_le_sq' (by linarith only [hSb, hSb0, hq]) (by linarith only [hSb])
    calc h0 / 4 * d2τ * (Sb + √(Sbr ^ 2 + Rb ^ 2)) ^ 2
        ≤ h0 / 4 * fx f2.hi * (√(fx Sbc) + √(Sbr ^ 2 + Rb ^ 2)) ^ 2 :=
          mul_le_mul (mul_le_mul_of_nonneg_left hF11 hh04) q1 (sq_nonneg _) (mul_nonneg hh04 hf2nn)
      _ = _ := by ring
  have e3 : d1a * (b0r * h0 * h0 / ((12 : ℕ) : ℝ)) = d1a * (b0r * h0 ^ 2 / 12) := by push_cast; ring
  have e3' : d1aR * (b0r * h0 * h0 / ((12 : ℕ) : ℝ)) = d1aR * (b0r * h0 ^ 2 / 12) := by push_cast; ring
  have e4 : |d1a| * h0 * fx (max rr.Er 0) / 2 ^ 1 = |d1a| * (h0 / 2) * Rb := by rw [hRb_def]; ring
  have e4' : |d1aR| * h0 * fx (max rr.Er 0) / 2 ^ 1 = |d1aR| * (h0 / 2) * Rb := by rw [hRb_def]; ring
  have hVB : _ ≤ rbar * phiS sR (a + Rb) + d1a * (b0r * h0 ^ 2 / 12) - |d1a| * (h0 / 2) * Rb -
      h0 / 4 * d2τ * (Sb + Sbr) ^ 2 := le_trans hvBlo (by linarith only [e1, e2, e3, e4])
  have hVA : _ ≤ rbar * phiS sR (a + Rb) + d1aR * (b0r * h0 ^ 2 / 12) - |d1aR| * (h0 / 2) * Rb -
      h0 / 4 * d2τ * (Sb + √(Sbr ^ 2 + Rb ^ 2)) ^ 2 := le_trans hvAlo (by linarith only [e1, e2', e3', e4'])
  have hv0 : 0 ≤ ∏ d, (realLo k hi d - realLo k lo d) :=
    Finset.prod_nonneg (fun d _ => by linarith [realLo_lt hv d])
  rw [volume_boxOf_prod hv, fx_max, fx_max, fx_zero]
  exact final_step hv0 hVB hVA hbr

end BHH
