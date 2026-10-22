/-
Soundness of the per-pair arithmetic of `entryF` (`W2/EntryDefs.lean`): `λ`, `μ`, the integrated remainder
`rad + tang` against `pairRem`, the pruning count `ν` against `nuCountSeg`, and the moment bounds `S1`, `S2`.
-/
import W2.EntryDefs
import W2.TabProps
import W2.FixSound

open Real

namespace BHH.W2

open W2C BHH.Cert BHH

lemma fx_one_pos : (0 : ℝ) < fx 1 := by unfold fx; positivity

lemma fx_ONE : fx ONE = 1 := by
  unfold fx; rw [show ((ONE : ℤ) : ℝ) = 2 ^ PR by norm_num [ONE, PR]]; field_simp

lemma fx_two_ONE : fx (2 * ONE) = 2 := by
  unfold fx; rw [show ((2 * ONE : ℤ) : ℝ) = 2 * 2 ^ PR by norm_num [ONE, PR]]; field_simp

lemma fx_add (a b : ℤ) : fx (a + b) = fx a + fx b := by unfold fx; push_cast; ring
lemma fx_sub (a b : ℤ) : fx (a - b) = fx a - fx b := by unfold fx; push_cast; ring
lemma fx_mono {a b : ℤ} (h : a ≤ b) : fx a ≤ fx b := fx_le_iff.mpr h
lemma fx_lt_of {a b : ℤ} (h : a < b) : fx a < fx b := fx_lt_iff.mpr h
lemma fx_min (a b : ℤ) : fx (Min.min a b) = Min.min (fx a) (fx b) := by
  rcases le_total a b with h | h
  · rw [min_eq_left h, min_eq_left (fx_mono h)]
  · rw [min_eq_right h, min_eq_right (fx_mono h)]
lemma fx_max (a b : ℤ) : fx (Max.max a b) = Max.max (fx a) (fx b) := by
  rcases le_total a b with h | h
  · rw [max_eq_right h, max_eq_right (fx_mono h)]
  · rw [max_eq_left h, max_eq_left (fx_mono h)]
lemma fx_natMul (n : ℕ) (a : ℤ) : fx ((n : ℤ) * a) = (n : ℝ) * fx a := by unfold fx; push_cast; ring
lemma fx_mul_two (a : ℤ) : fx (2 * a) = 2 * fx a := by unfold fx; push_cast; ring

/-- `shrU (a * b) PR + 1` bounds the product of the two fixed-point numbers from above. -/
lemma fx_shrU_mul (a b : ℤ) : fx a * fx b ≤ fx (shrU (a * b) PR + 1) := by
  have h := le_shrU (a * b) PR
  rw [fx_add]
  have h1 : fx a * fx b = ((a * b : ℤ) : ℝ) / 2 ^ PR / 2 ^ PR := by unfold fx; push_cast; field_simp
  have h2 : ((a * b : ℤ) : ℝ) / 2 ^ PR / 2 ^ PR ≤ fx (shrU (a * b) PR) := by
    unfold fx; exact div_le_div_of_nonneg_right h (by positivity)
  linarith [fx_one_pos]

/-- `shrU (a * b) PR` bounds the product from above. -/
lemma fx_shrU_mul' (a b : ℤ) : fx a * fx b ≤ fx (shrU (a * b) PR) := by
  have h := le_shrU (a * b) PR
  have h1 : fx a * fx b = ((a * b : ℤ) : ℝ) / 2 ^ PR / 2 ^ PR := by unfold fx; push_cast; field_simp
  rw [h1]; unfold fx; exact div_le_div_of_nonneg_right h (by positivity)

lemma mem_pt_iv (n : ℤ) : ivMem (fx n) ⟨n, n⟩ := Iv.mem_pt n

/-! ## `λ` and `μ` -/

lemma useFirst_dhi {dx : ℤ} (h : useFirstOf dx) : fx dx < 2 := by
  have h1 : dx * 100 < 198 * ONE := h.1
  have h2 : (dx : ℝ) * 100 < 198 * 2 ^ PR := by
    have : ((dx * 100 : ℤ) : ℝ) < ((198 * ONE : ℤ) : ℝ) := by exact_mod_cast h1
    rw [show ((198 * ONE : ℤ) : ℝ) = 198 * 2 ^ PR by norm_num [ONE, PR]] at this
    push_cast at this; exact this
  unfold fx
  rw [div_lt_iff₀ (by positivity)]
  nlinarith [pow_pos (two_pos : (0 : ℝ) < 2) PR]

/-- `λ ≥ 1/√(4 - d⁺²)` for the first choice (when the square root has a positive lower end). -/
theorem lam_spec {dx : ℤ} (hf : useFirstOf dx) (hpos : 0 < (Iv.sqrt (Iv.sub (Iv.int 4) (Iv.sqr ⟨dx, dx⟩))).lo) :
    1 / √(4 - fx dx ^ 2) ≤ fx (lamOf dx) := by
  have h1 : ivMem (fx dx ^ 2) (Iv.sqr ⟨dx, dx⟩) := Iv.mem_sqr (mem_pt_iv dx)
  have h2 : ivMem (4 - fx dx ^ 2) (Iv.sub (Iv.int 4) (Iv.sqr ⟨dx, dx⟩)) := by
    have := Iv.mem_sub (Iv.mem_int 4) h1; push_cast at this; exact this
  have h3 := Iv.mem_inv (Iv.mem_sqrt h2) hpos
  unfold lamOf
  rw [if_pos hf]
  exact ivMem_hi_le h3

theorem lam_nonneg {dx : ℤ} (hf : useFirstOf dx) (hpos : 0 < (Iv.sqrt (Iv.sub (Iv.int 4) (Iv.sqr ⟨dx, dx⟩))).lo) :
    0 ≤ fx (lamOf dx) :=
  le_trans (by positivity) (lam_spec hf hpos)

lemma lam_zero {dx : ℤ} (hf : ¬ useFirstOf dx) : lamOf dx = 0 := by unfold lamOf; rw [if_neg hf]

lemma mu_zero {dn dx : ℤ} (hf : useFirstOf dx) : muOf dn dx = 0 := by unfold muOf; rw [if_pos hf]

/-- `μ ≥ 2 arcsin(min(d⁺, 2)/2) - 2 arcsin(d⁻/2)` and `μ ≥ 0` for the second choice. -/
theorem mu_spec {dn dx : ℤ} (hf : ¬ useFirstOf dx) :
    2 * Real.arcsin (min (fx dx) 2 / 2) - 2 * Real.arcsin (fx dn / 2) ≤ fx (muOf dn dx) ∧ 0 ≤ fx (muOf dn dx) := by
  unfold muOf
  rw [if_neg hf]
  simp only
  rw [fx_max]
  refine ⟨le_trans ?_ (le_max_left _ _), le_trans (by unfold fx; simp) (le_max_right _ _)⟩
  rw [fx_mul_two, fx_sub]
  have hw : fx (asinIv (Iv.div2e ⟨dn, dn⟩ 1)).lo ≤ Real.arcsin (fx dn / 2) := by
    have := asinIv_spec (Iv.mem_div2e (mem_pt_iv dn) 1)
    simp only [pow_one] at this
    exact ivMem_lo_le this
  have hu : Real.arcsin (min (fx dx) 2 / 2) ≤
      fx (if dx < 2 * ONE then (asinIv (Iv.div2e ⟨dx, dx⟩ 1)).hi else halfPiHi) := by
    split_ifs with h2
    · have hlt : fx dx < 2 := by have := fx_lt_of h2; rwa [fx_two_ONE] at this
      rw [min_eq_left hlt.le]
      have := asinIv_spec (Iv.mem_div2e (mem_pt_iv dx) 1)
      simp only [pow_one] at this
      exact ivMem_hi_le this
    · exact (Real.arcsin_le_pi_div_two _).trans le_halfPiHi
  linarith

/-! ## `rad + tang` -/

/-- The code's `rad + tang` of a pair bounds `pairRem` (given `S1`, `S2` bounds and `0 < d⁻`). -/
theorem radTang_spec {dn dx S1 S2 : ℤ} {S1r S2r : ℝ} (hdn : 0 < dn)
    (hpos : useFirstOf dx → 0 < (Iv.sqrt (Iv.sub (Iv.int 4) (Iv.sqr ⟨dx, dx⟩))).lo)
    (hS1 : S1r ≤ fx S1) (hS2 : S2r ≤ fx S2) (hS1r : 0 ≤ S1r) (hS2r : 0 ≤ S2r) :
    pairRem (fx dn) (fx dx) (decide (useFirstOf dx)) S1r S2r ≤
      fx ((if useFirstOf dx then shrU (lamOf dx * S2) PR + 1 else shrU (muOf dn dx * S1) PR + 1) +
        Min.min ((Iv.div ⟨S2, S2⟩ ⟨dn, dn⟩).hi) (shrU (piHi * S1) PR + 1)) := by
  unfold pairRem
  rw [fx_add, fx_min]
  have hdnr : 0 < fx dn := fx_pos_iff.mpr hdn
  have htang : min (S2r / fx dn) (π * S1r) ≤
      min (fx (Iv.div ⟨S2, S2⟩ ⟨dn, dn⟩).hi) (fx (shrU (piHi * S1) PR + 1)) := by
    apply min_le_min
    · have := Iv.mem_div (mem_pt_iv S2) (mem_pt_iv dn) hdn
      exact (div_le_div_of_nonneg_right hS2 hdnr.le).trans (ivMem_hi_le this)
    · calc π * S1r ≤ fx piHi * fx S1 :=
            mul_le_mul le_piHi hS1 hS1r (le_trans (by positivity) le_piHi)
        _ ≤ fx (shrU (piHi * S1) PR + 1) := fx_shrU_mul _ _
  have hrad : (if decide (useFirstOf dx) = true then S2r / √(4 - fx dx ^ 2)
        else (2 * Real.arcsin (min (fx dx) 2 / 2) - 2 * Real.arcsin (fx dn / 2)) * S1r) ≤
      fx (if useFirstOf dx then shrU (lamOf dx * S2) PR + 1 else shrU (muOf dn dx * S1) PR + 1) := by
    by_cases hf : useFirstOf dx
    · rw [if_pos (decide_eq_true hf), if_pos hf]
      have hl := lam_spec hf (hpos hf)
      calc S2r / √(4 - fx dx ^ 2) = (1 / √(4 - fx dx ^ 2)) * S2r := by ring
        _ ≤ fx (lamOf dx) * fx S2 := mul_le_mul hl hS2 hS2r (lam_nonneg hf (hpos hf))
        _ ≤ _ := fx_shrU_mul _ _
    · rw [if_neg (by simpa using hf), if_neg hf]
      obtain ⟨hm, hm0⟩ := mu_spec (dn := dn) hf
      calc (2 * Real.arcsin (min (fx dx) 2 / 2) - 2 * Real.arcsin (fx dn / 2)) * S1r
          ≤ fx (muOf dn dx) * S1r := mul_le_mul_of_nonneg_right hm hS1r
        _ ≤ fx (muOf dn dx) * fx S1 := mul_le_mul_of_nonneg_left hS1 hm0
        _ ≤ _ := fx_shrU_mul _ _
  linarith

/-! ## `S1`, `S2` -/

lemma sqrt_pt_hi (m : ℤ) : √(fx m) ≤ fx (Iv.sqrt ⟨m, m⟩).hi := ivMem_hi_le (Iv.mem_sqrt (mem_pt_iv m))

lemma sqrt_pt_lo (m : ℤ) : fx (Iv.sqrt ⟨m, m⟩).lo ≤ √(fx m) := ivMem_lo_le (Iv.mem_sqrt (mem_pt_iv m))

/-- The moment bounds of the code dominate `pairS1`, `pairS2` for `m0 = M0 + e0²`, `m2 = M2 + e2²`. -/
theorem S12_spec {mom0 mom2 e0 e2 : ℤ} {M0 M2 : ℝ} (hM0 : M0 ≤ fx mom0) (hM2 : M2 ≤ fx mom2) (hM0n : 0 ≤ M0)
    (hM2n : 0 ≤ M2) :
    let m0 := mom0 + shrU (e0 * e0) PR + 1
    let m2 := mom2 + shrU (e2 * e2) PR + 1
    let sq0 := (Iv.sqrt ⟨m0, m0⟩).hi
    let sq2 := (Iv.sqrt ⟨m2, m2⟩).hi
    ∀ p : Fin 3, ∀ q : Fin 3,
      (p = 0 ∧ q = 1 → pairS1 (M0 + fx e0 ^ 2) (M2 + fx e2 ^ 2) p q ≤ fx sq0 ∧
          pairS2 (M0 + fx e0 ^ 2) (M2 + fx e2 ^ 2) p q ≤ fx m0) ∧
      (p = 1 ∧ q = 2 → pairS1 (M0 + fx e0 ^ 2) (M2 + fx e2 ^ 2) p q ≤ fx sq2 ∧
          pairS2 (M0 + fx e0 ^ 2) (M2 + fx e2 ^ 2) p q ≤ fx m2) ∧
      (p = 0 ∧ q = 2 → pairS1 (M0 + fx e0 ^ 2) (M2 + fx e2 ^ 2) p q ≤ fx (sq0 + sq2) ∧
          pairS2 (M0 + fx e0 ^ 2) (M2 + fx e2 ^ 2) p q ≤ fx (m0 + m2 + 2 * shrU (sq0 * sq2) PR + 2)) := by
  intro m0 m2 sq0 sq2 p q
  have hm0 : M0 + fx e0 ^ 2 ≤ fx m0 := by
    have := fx_shrU_mul' e0 e0
    simp only [m0, fx_add]; nlinarith [fx_one_pos]
  have hm2 : M2 + fx e2 ^ 2 ≤ fx m2 := by
    have := fx_shrU_mul' e2 e2
    simp only [m2, fx_add]; nlinarith [fx_one_pos]
  have hs0 : √(M0 + fx e0 ^ 2) ≤ fx sq0 := (Real.sqrt_le_sqrt hm0).trans (sqrt_pt_hi m0)
  have hs2 : √(M2 + fx e2 ^ 2) ≤ fx sq2 := (Real.sqrt_le_sqrt hm2).trans (sqrt_pt_hi m2)
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · obtain ⟨rfl, rfl⟩ := h
    simp only [pairS1, pairS2, true_and, if_true]
    exact ⟨hs0, hm0⟩
  · obtain ⟨rfl, rfl⟩ := h
    simp only [pairS1, pairS2]
    simp only [Fin.isValue, show (1 : Fin 3) ≠ 0 by decide, false_and, if_false, true_and, if_true]
    exact ⟨hs2, hm2⟩
  · obtain ⟨rfl, rfl⟩ := h
    simp only [pairS1, pairS2]
    simp only [Fin.isValue, show (2 : Fin 3) ≠ 1 by decide, show (0 : Fin 3) ≠ 1 by decide, and_false,
      false_and, if_false]
    refine ⟨by rw [fx_add]; linarith, ?_⟩
    have hp := fx_shrU_mul' sq0 sq2
    have hsq0 : 0 ≤ √(M0 + fx e0 ^ 2) := Real.sqrt_nonneg _
    have hsq2 : 0 ≤ √(M2 + fx e2 ^ 2) := Real.sqrt_nonneg _
    have h2 : √(M0 + fx e0 ^ 2) * √(M2 + fx e2 ^ 2) ≤ fx sq0 * fx sq2 :=
      mul_le_mul hs0 hs2 hsq2 (hsq0.trans hs0)
    rw [fx_add, fx_add, fx_add, fx_mul_two]
    have : fx 2 = 2 * fx 1 := by unfold fx; push_cast; ring
    rw [this]
    nlinarith [fx_one_pos]

/-! ## `ν` -/

lemma nuCountSeg_le_two {k : ℕ} (c : Fin k → Pt) (eps : Fin k → ℝ) (dlo dhi : Fin k → Fin k → ℝ)
    (first : Fin k → Fin k → Bool) (i j : Fin k) : nuCountSeg c eps dlo dhi first i j ≤ 2 := by
  unfold nuCountSeg
  simp only
  split_ifs <;> omega

lemma Tseg_le {dn dx wv : ℤ} (hdn : 0 < dn) (hw : 0 ≤ fx wv)
    (hpos : useFirstOf dx → 0 < (Iv.sqrt (Iv.sub (Iv.int 4) (Iv.sqr ⟨dx, dx⟩))).lo) :
    Tseg (fx dn) (fx dx) (decide (useFirstOf dx)) (fx wv) ≤
      fx (shrU (lamOf dx * wv) PR + 1 + muOf dn dx + Min.min ((Iv.div ⟨wv, wv⟩ ⟨dn, dn⟩).hi) piHi) := by
  unfold Tseg
  rw [fx_add, fx_add, fx_min]
  have hdnr : 0 < fx dn := fx_pos_iff.mpr hdn
  have hmin : min (fx wv / fx dn) π ≤ min (fx (Iv.div ⟨wv, wv⟩ ⟨dn, dn⟩).hi) (fx piHi) :=
    min_le_min (ivMem_hi_le (Iv.mem_div (mem_pt_iv wv) (mem_pt_iv dn) hdn)) le_piHi
  by_cases hf : useFirstOf dx
  · rw [if_pos (decide_eq_true hf), mu_zero hf]
    have hl := lam_spec hf (hpos hf)
    have h1 : fx wv / √(4 - fx dx ^ 2) ≤ fx (shrU (lamOf dx * wv) PR + 1) :=
      calc fx wv / √(4 - fx dx ^ 2) = (1 / √(4 - fx dx ^ 2)) * fx wv := by ring
        _ ≤ fx (lamOf dx) * fx wv := mul_le_mul_of_nonneg_right hl hw
        _ ≤ _ := fx_shrU_mul _ _
    have h0 : fx (0 : ℤ) = 0 := by unfold fx; simp
    rw [h0]; linarith
  · rw [if_neg (by simpa using hf), lam_zero hf]
    obtain ⟨hm, -⟩ := mu_spec (dn := dn) hf
    have h1 : 0 ≤ fx (shrU (0 * wv) PR + 1) := by
      rw [zero_mul, fx_add]
      have : shrU 0 PR = 0 := by unfold shrU; simp
      rw [this]; unfold fx; positivity
    linarith

/-- The pruning count of the code dominates `ν_ij` (pair `p` with endpoints `i`, `j` and third point `l`). -/
theorem nu_spec (hDS : DistSound) (prune : Bool) (C : ECore) (c : Fin 3 → Pt)
    (hc : ∀ i : Fin 3, c i = (fx (C.pts.getD i.val (0, 0)).1, fx (C.pts.getD i.val (0, 0)).2))
    (eps : Fin 3 → ℝ) (heps : ∀ i : Fin 3, eps i = fx (C.epsR.getD i.val 0)) (hepsn : ∀ i, 0 ≤ eps i)
    (dlo dhi : Fin 3 → Fin 3 → ℝ) (first : Fin 3 → Fin 3 → Bool) (p : ℕ) (i j l : Fin 3)
    (hijl : pairIJL p = (i.val, j.val, l.val)) (hli : l ≠ i) (hlj : l ≠ j) {dn dx : ℤ} (hdn : 0 < dn)
    (hdlo : dlo i j = fx dn) (hdhi : dhi i j = fx dx) (hfirst : first i j = decide (useFirstOf dx))
    (hpos : useFirstOf dx → 0 < (Iv.sqrt (Iv.sub (Iv.int 4) (Iv.sqr ⟨dx, dx⟩))).lo)
    (hnd : prune = true → ∀ ax ay bx by_ : ℤ, C.pts.getD i.val (0, 0) = (ax, ay) → C.pts.getD j.val (0, 0) = (bx, by_) →
      0 < (bx - ax) * (bx - ax) + (by_ - ay) * (by_ - ay) →
      (bx - ax) * (bx - ax) + (by_ - ay) * (by_ - ay) < 4 * ONE * ONE →
      0 < (Iv.sqrt (Iv.add (Iv.sqr (Iv.pt (bx - ax))) (Iv.sqr (Iv.pt (by_ - ay))))).lo) :
    nuCountSeg c eps dlo dhi first i j ≤
      nuOf prune C.pts (if prune then C.epsR else [0, 0, 0]) (lamOf dx) (muOf dn dx) dn p := by
  have h2 := nuCountSeg_le_two c eps dlo dhi first i j
  cases prune with
  | false => unfold nuOf; simpa using h2
  | true =>
    classical
    unfold nuOf
    simp only [Bool.not_true, Bool.false_eq_true, if_false, if_true]
    rw [hijl]
    simp only
    rcases hA : C.pts.getD i.val (0, 0) with ⟨ax, ay⟩
    rcases hB : C.pts.getD j.val (0, 0) with ⟨bx, by_⟩
    rcases hL : C.pts.getD l.val (0, 0) with ⟨lx, ly⟩
    simp only
    by_cases hdc : 0 < (bx - ax) * (bx - ax) + (by_ - ay) * (by_ - ay) ∧
        (bx - ax) * (bx - ax) + (by_ - ay) * (by_ - ay) < 4 * ONE * ONE
    · rw [if_pos hdc]
      have hnd' := hnd rfl ax ay bx by_ hA hB hdc.1 hdc.2
      have hci : c i = (fx ax, fx ay) := by rw [hc i, hA]
      have hcj : c j = (fx bx, fx by_) := by rw [hc j, hB]
      have hcl : c l = (fx lx, fx ly) := by rw [hc l, hL]
      have hsq : sqDist (fx ax, fx ay) (fx bx, fx by_) =
          (((bx - ax) * (bx - ax) + (by_ - ay) * (by_ - ay) : ℤ) : ℝ) / (2 ^ PR * 2 ^ PR) := by
        unfold sqDist fx; push_cast; field_simp; ring
      have hONE2 : (((4 * ONE * ONE : ℤ)) : ℝ) = 4 * (2 ^ PR * 2 ^ PR) := by norm_num [ONE, PR]
      have hsq0 : 0 < sqDist (fx ax, fx ay) (fx bx, fx by_) := by
        rw [hsq]; apply div_pos (by exact_mod_cast hdc.1) (by positivity)
      have hsq4 : sqDist (fx ax, fx ay) (fx bx, fx by_) < 4 := by
        rw [hsq, div_lt_iff₀ (by positivity)]
        have : (((bx - ax) * (bx - ax) + (by_ - ay) * (by_ - ay) : ℤ) : ℝ) < ((4 * ONE * ONE : ℤ) : ℝ) := by
          exact_mod_cast hdc.2
        rw [hONE2] at this; linarith
      obtain ⟨hd1, hd2⟩ := hDS.2.2 ax ay bx by_ lx ly hsq0 hsq4 hnd'
      have hdc' : 0 < edist2 (c i) (c j) ∧ edist2 (c i) (c j) < 2 := by
        rw [hci, hcj]
        unfold edist2
        refine ⟨Real.sqrt_pos.mpr hsq0, ?_⟩
        rw [show (2 : ℝ) = √4 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
        exact Real.sqrt_lt_sqrt hsq0.le hsq4
      have hei : eps i = fx (C.epsR.getD i.val 0) := heps i
      have hej : eps j = fx (C.epsR.getD j.val 0) := heps j
      have hel : eps l = fx (C.epsR.getD l.val 0) := heps l
      have hT : Tseg (dlo i j) (dhi i j) (first i j) (eps i + eps j) ≤
          fx (shrU (lamOf dx * (C.epsR.getD i.val 0 + C.epsR.getD j.val 0)) PR + 1 + muOf dn dx +
            Min.min ((Iv.div ⟨C.epsR.getD i.val 0 + C.epsR.getD j.val 0, C.epsR.getD i.val 0 + C.epsR.getD j.val 0⟩
              ⟨dn, dn⟩).hi) piHi) := by
        rw [hdlo, hdhi, hfirst, hei, hej, ← fx_add]
        exact Tseg_le hdn (by rw [fx_add, ← hei, ← hej]; linarith [hepsn i, hepsn j]) hpos
      have key : ∀ (P : Pt) (d : ℤ), edist2 P (c l) ≤ fx d →
          (if certCoveredSeg c eps dlo dhi first i j P then 0 else 1) ≤
            (if d + C.epsR.getD i.val 0 +
                (shrU (lamOf dx * (C.epsR.getD i.val 0 + C.epsR.getD j.val 0)) PR + 1 + muOf dn dx +
                  Min.min ((Iv.div ⟨C.epsR.getD i.val 0 + C.epsR.getD j.val 0,
                    C.epsR.getD i.val 0 + C.epsR.getD j.val 0⟩ ⟨dn, dn⟩).hi) piHi) +
                C.epsR.getD l.val 0 < ONE then 0 else 1) := by
        intro P d hPd
        by_cases hcode : d + C.epsR.getD i.val 0 +
                (shrU (lamOf dx * (C.epsR.getD i.val 0 + C.epsR.getD j.val 0)) PR + 1 + muOf dn dx +
                  Min.min ((Iv.div ⟨C.epsR.getD i.val 0 + C.epsR.getD j.val 0,
                    C.epsR.getD i.val 0 + C.epsR.getD j.val 0⟩ ⟨dn, dn⟩).hi) piHi) +
                C.epsR.getD l.val 0 < ONE
        · have hcert : certCoveredSeg c eps dlo dhi first i j P := by
            refine ⟨l, hli, hlj, ?_⟩
            have hlt := fx_lt_of hcode
            rw [fx_ONE, fx_add, fx_add, fx_add] at hlt
            linarith [hei, hel]
          rw [if_pos hcert]; exact Nat.zero_le _
        · rw [if_neg hcode]; split_ifs <;> omega
      have k1 := key (vertexPts (c i) (c j)).1 (vertexDistHi ax ay bx by_ lx ly).1
        (by rw [hci, hcj, hcl]; exact hd1)
      have k2 := key (vertexPts (c i) (c j)).2 (vertexDistHi ax ay bx by_ lx ly).2
        (by rw [hci, hcj, hcl]; exact hd2)
      unfold nuCountSeg
      simp only
      rw [if_pos hdc']
      exact Nat.add_le_add k1 k2
    · rw [if_neg hdc]; exact h2

end BHH.W2
