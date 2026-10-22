/-
Module D, part 6: per-pair bounds of the code's remainder (`remPair`) against the real terms of `ϱ`, `R_max`, `E ϱ`,
`(E ϱ²)^{1/2}` (the shapes of module C's `RemMaxProp` and `RemMomentsProp`).
-/
import BHH.LeafSound.Prune
import BHH.Box.Props

open BHH.Cert Real

noncomputable section

namespace BHH

/-- the real corners of a fixed-point box -/
def realLo (k : ℕ) (lo : List ℤ) : Fin (mDim k) → ℝ := fun d => fx (lo.getD d.val 0)

lemma xget_realLo {k : ℕ} {lo : List ℤ} {d : ℕ} (hd : d < mDim k) : xget (realLo k lo) d = fx (lo.getD d 0) := by
  simp [xget, hd, realLo]

/-- the half-sides of module C are the code's half-sides -/
lemma halfSides_eq {k : ℕ} (hk : 3 ≤ k) (lo hi : List ℤ) (j : Fin k) :
    halfSides k (realLo k lo) (realLo k hi) j = halfOf ((ptBoxes k lo hi).getD j.val default) := by
  have hm : mDim k = 2 * k - 3 := rfl
  unfold halfSides halfOf
  rw [ptBoxes_getD]
  by_cases h0 : j.val = 0
  · simp [h0, fx_zero]
  · by_cases h1 : j.val = 1
    · simp only [h0, h1, ite_false, ite_true, listGet]
      rw [xget_realLo (show 0 < mDim k by rw [hm]; omega), xget_realLo (show 0 < mDim k by rw [hm]; omega)]
      simp [fx_zero]
    · simp only [h0, h1, ite_false, listGet]
      have hj := j.isLt
      rw [xget_realLo (show 2 * j.val - 3 < mDim k by rw [hm]; omega),
        xget_realLo (show 2 * j.val - 3 < mDim k by rw [hm]; omega),
        xget_realLo (show 2 * j.val - 2 < mDim k by rw [hm]; omega),
        xget_realLo (show 2 * j.val - 2 < mDim k by rw [hm]; omega)]

lemma moments_getD (k : ℕ) (lo hi : List ℤ) (i : Fin k) :
    ((ptBoxes k lo hi).map moments).getD i.val default = moments ((ptBoxes k lo hi).getD i.val default) := by
  have hl : i.val < (ptBoxes k lo hi).length := by simp [ptBoxes]
  rw [List.getD_eq_getElem _ _ (by simpa using hl), List.getElem_map, List.getD_eq_getElem _ _ hl]

/-- a pair skipped by the code (`(d^-)² ≥ 4`) has `d^- ≥ 2` -/
lemma dlo_ge_two_of_skip {P Q : PtBox} (h : 4 * ONE * ONE ≤ (d2minmax P Q).1) :
    2 ≤ √(dminSq (rectOf P) (rectOf Q)) := by
  rw [dminSq_rectOf]
  have : (4:ℝ) ≤ ((d2minmax P Q).1 : ℝ) / (2 : ℝ) ^ (2 * PR) := by
    rw [← ONE_sq4_cast]; gcongr
  exact (Real.le_sqrt (by norm_num) (by linarith)).mpr (by nlinarith)

/-- the moment quantities of module C at the points of a valid box, with their code enclosures -/
lemma mom_enclosures {k : ℕ} (hk : 3 ≤ k) {lo hi : List ℤ} (hv : ValidBox k lo hi) (i : Fin k) :
    let σ := halfSides k (realLo k lo) (realLo k hi) i
    let M := moments ((ptBoxes k lo hi).getD i.val default)
    ivMem (boxRects k lo hi i).eps M.1 ∧ ivMem √(m2pt σ) M.2.1 ∧ ivMem (m2pt σ) M.2.2.1 ∧ ivMem (m4pt σ) M.2.2.2 := by
  intro σ M
  obtain ⟨hx, hy⟩ := ptBoxes_even hk hv i
  have hs : σ = halfOf ((ptBoxes k lo hi).getD i.val default) := halfSides_eq hk lo hi i
  obtain ⟨h1, h2, h3, h4⟩ := moments_sound hx hy
  refine ⟨h1, ?_, ?_, ?_⟩
  · rw [hs]; unfold m2pt; exact h2
  · rw [hs]; unfold m2pt; exact h3
  · rw [hs]; unfold m4pt; exact h4

lemma fx_add' (a b : ℤ) : fx (a + b) = fx a + fx b := by unfold fx; push_cast; ring

lemma fx_min' (a b : ℤ) : fx (Min.min a b) = Min.min (fx a) (fx b) := by
  unfold fx; rw [Int.cast_min, min_div_div_right (by positivity)]

lemma fx_mul_le_shrU (x y : ℤ) : fx x * fx y ≤ fx (shrU (x * y) PR) := by
  have h := le_shrU (x * y) PR
  unfold fx
  calc (x : ℝ) / 2 ^ PR * ((y : ℝ) / 2 ^ PR) = ((x * y : ℤ) : ℝ) / 2 ^ PR / 2 ^ PR := by push_cast; ring
    _ ≤ ((shrU (x * y) PR : ℤ) : ℝ) / 2 ^ PR := by gcongr

lemma m2pt_nonneg (σ : ℝ × ℝ) : 0 ≤ m2pt σ := by unfold m2pt; positivity

lemma m4pt_nonneg (σ : ℝ × ℝ) : 0 ≤ m4pt σ := by unfold m4pt; positivity

/-- `ν X ≤ n Y` from `0 ≤ ν ≤ n` and `0 ≤ X ≤ Y` -/
lemma count_mul_le {ν n X Y : ℝ} (hν0 : 0 ≤ ν) (hνn : ν ≤ n) (hX0 : 0 ≤ X) (hXY : X ≤ Y) : ν * X ≤ n * Y :=
  calc ν * X ≤ ν * Y := mul_le_mul_of_nonneg_left hXY hν0
    _ ≤ n * Y := mul_le_mul_of_nonneg_right hνn (le_trans hX0 hXY)

/-- the rectangles of a valid box are nonempty, so `d⁻ ≤ d⁺` -/
lemma dminSq_le_dmaxSq_box {k : ℕ} (hk : 3 ≤ k) {lo hi : List ℤ} (hv : ValidBox k lo hi) (i j : Fin k) :
    dminSq (boxRects k lo hi i) (boxRects k lo hi j) ≤ dmaxSq (boxRects k lo hi i) (boxRects k lo hi j) := by
  have hx : realLo k lo ∈ (boxOf lo hi : Set (Fin (mDim k) → ℝ)) := by
    rw [mem_boxOf_iff]
    intro d
    refine ⟨le_refl _, ?_⟩
    show fx (lo.getD d.val 0) < fx (hi.getD d.val 0)
    unfold fx
    have h := (hv.2.2.1 d.val d.isLt).1
    have h' : ((lo.getD d.val 0 : ℤ) : ℝ) < ((hi.getD d.val 0 : ℤ) : ℝ) := by exact_mod_cast h
    gcongr
  obtain ⟨h1, h2⟩ := VertexRect.dminSq_le_sqDist (mem_boxRects hx hk i) (mem_boxRects hx hk j)
  linarith

/-- Per-pair soundness of `remPair`: with `ν` vertices of the pair not certified covered, the code's three
contributions bound `ν ε T`, `ν (λ E2 + μ E1 + min(E2/d⁻, π E1))` and `ν √(3(λ² E4 + μ² E2 + min(E4/d⁻², π² E2)))`. -/
theorem remPair_sound {k : ℕ} (hk : 3 ≤ k) {lo hi : List ℤ} (hv : ValidBox k lo hi)
    {cs : ℤ → Iv × Iv} (hcs : CosSinSound cs) (asinC : AsinFn) (i j : Fin k) (hij : i < j)
    (first : Fin k → Fin k → Bool)
    (hfirst : first i j = decide ((d2minmax ((ptBoxes k lo hi).getD i.val default)
      ((ptBoxes k lo hi).getD j.val default)).2 < thr198))
    {nv : ℕ} {a b c : ℤ}
    (h : remPair cs asinC (ptBoxes k lo hi) ((ptBoxes k lo hi).map moments) i.val j.val
      (d2minmax ((ptBoxes k lo hi).getD i.val default) ((ptBoxes k lo hi).getD j.val default)).1
      (d2minmax ((ptBoxes k lo hi).getD i.val default) ((ptBoxes k lo hi).getD j.val default)).2 =
        some (nv, a, b, c)) :
    let R := boxRects k lo hi
    let dlo := √(dminSq (R i) (R j))
    let dhi := √(dmaxSq (R i) (R j))
    let σ := halfSides k (realLo k lo) (realLo k hi)
    let E1 := √(m2pt (σ i)) + √(m2pt (σ j))
    let E2 := m2pt (σ i) + m2pt (σ j) + 2 * √(m2pt (σ i)) * √(m2pt (σ j))
    let E4 := 8 * (m4pt (σ i) + m4pt (σ j))
    let ν : ℝ := nuCount R first i j
    dlo < 2 →
      ν * ((R i).eps + (R j).eps) * Tseg dlo dhi (first i j) ((R i).eps + (R j).eps) ≤ nv * fx a ∧
      ν * (lamT dhi (first i j) * E2 + muT dlo dhi (first i j) * E1 + min (E2 / dlo) (π * E1)) ≤ nv * fx b ∧
      ν * √(3 * lamT dhi (first i j) ^ 2 * E4 + 3 * muT dlo dhi (first i j) ^ 2 * E2 +
        3 * min (E4 / dlo ^ 2) (π ^ 2 * E2)) ≤ nv * fx c := by
  intro R dlo dhi σ E1 E2 E4 ν hdlo
  set Pi := (ptBoxes k lo hi).getD i.val default with hPi
  set Pj := (ptBoxes k lo hi).getD j.val default with hPj
  set d2mn := (d2minmax Pi Pj).1 with hd2mn
  set d2mx := (d2minmax Pi Pj).2 with hd2mx
  unfold remPair at h
  by_cases hskip : 4 * ONE * ONE ≤ d2mn
  · exact absurd (dlo_ge_two_of_skip hskip) (not_le.mpr hdlo)
  rw [if_neg hskip] at h
  by_cases hneg : d2mn ≤ 0
  · rw [if_pos hneg] at h; exact absurd h (by simp)
  rw [if_neg hneg] at h
  rw [moments_getD, moments_getD] at h
  rcases hMi : moments ((ptBoxes k lo hi).getD i.val default) with ⟨deli, m1i, m2i, m4i⟩
  rcases hMj : moments ((ptBoxes k lo hi).getD j.val default) with ⟨delj, m1j, m2j, m4j⟩
  rw [hMi, hMj] at h
  dsimp only at h
  set d2mnI := (Iv.pt d2mn).div2e PR with hd2mnI
  set dmn := d2mnI.sqrt with hdmn
  set q4 := ((Iv.pt (4 * ONE * ONE - d2mx)).div2e PR).sqrt with hq4
  set dl := deli.add delj with hdl
  set c1 : ℤ := (if d2mx < thr198 then q4.inv.hi else 0) with hc1
  set up : ℤ := (if d2mx < 4 * ONE * ONE then asinHi cs asinC (shrU ((Iv.pt d2mx).div2e PR).sqrt.hi 1)
      else shrU piHi 1) with hup
  set lw : ℤ := asinLo cs asinC (shrD dmn.lo 1) with hlw
  set c0 : ℤ := (if d2mx < thr198 then 0 else 2 * (up - lw)) with hc0
  set tcap : ℤ := min (dl.div dmn).hi piHi with htcap
  set motion : ℤ := shrU (c1 * dl.hi) PR + c0 + tcap with hmotion
  set nvc := nvCount (ptBoxes k lo hi) (List.map moments (ptBoxes k lo hi)) i.val j.val deli motion with hnvc
  -- enclosures of the moments
  obtain ⟨hdeli, hm1i, hm2i, hm4i⟩ := mom_enclosures hk hv i
  obtain ⟨hdelj, hm1j, hm2j, hm4j⟩ := mom_enclosures hk hv j
  rw [hMi] at hdeli hm1i hm2i hm4i
  rw [hMj] at hdelj hm1j hm2j hm4j
  simp only at hdeli hm1i hm2i hm4i hdelj hm1j hm2j hm4j
  have hdlI : ivMem ((R i).eps + (R j).eps) dl := Iv.mem_add hdeli hdelj
  -- the real distances
  have hmin : dminSq (R i) (R j) = (d2mn : ℝ) / (2 : ℝ) ^ (2 * PR) := dminSq_rectOf Pi Pj
  have hmax : dmaxSq (R i) (R j) = (d2mx : ℝ) / (2 : ℝ) ^ (2 * PR) := dmaxSq_rectOf Pi Pj
  have hd2I : ivMem (dminSq (R i) (R j)) d2mnI := by rw [hmin]; exact mem_d2I d2mn
  have hdmnI : ivMem dlo dmn := Iv.mem_sqrt hd2I
  have hdlo0 : 0 ≤ dlo := Real.sqrt_nonneg _
  have hdhi0 : 0 ≤ dhi := Real.sqrt_nonneg _
  have heps0 : 0 ≤ (R i).eps + (R j).eps := by
    unfold Rect.eps; positivity
  -- the guard
  by_cases hg : dmn.lo ≤ 0 ∨ d2mnI.lo ≤ 0 ∨ (d2mx < thr198 ∧ q4.lo ≤ 0)
  · rw [if_pos hg] at h; exact absurd h (by simp)
  rw [if_neg hg] at h
  push_neg at hg
  obtain ⟨hdmnpos, hd2Ipos, hq4g⟩ := hg
  have hfx2 : fx 2 = 2 / 2 ^ PR := by unfold fx; norm_num
  have hdhisq : dhi ^ 2 = dmaxSq (R i) (R j) := Real.sq_sqrt (VertexRect.dmaxSq_nonneg _ _)
  have hfst : first i j = decide (d2mx < thr198) := hfirst
  -- λ-bound
  have hlam : (if first i j then 1 / √(4 - dhi ^ 2) else 0) ≤ fx c1 ∧ 0 ≤ c1 := by
    rw [hfst]
    by_cases hf : d2mx < thr198
    · simp only [hf, decide_true, ite_true, hc1]
      have hq4pos : 0 < q4.lo := hq4g hf
      have hq4I : ivMem √(4 - dhi ^ 2) q4 := by
        apply Iv.mem_sqrt
        have := mem_d2I (4 * ONE * ONE - d2mx)
        rw [hdhisq, hmax]
        have h4 := ONE_sq4_cast
        have e : ((4 * ONE * ONE - d2mx : ℤ) : ℝ) / (2 : ℝ) ^ (2 * PR) = 4 - (d2mx : ℝ) / (2 : ℝ) ^ (2 * PR) := by
          rw [Int.cast_sub, sub_div, h4]
        rw [e] at this; exact this
      have hinv := Iv.mem_inv hq4I hq4pos
      have hle := ivMem_hi_le hinv
      refine ⟨hle, ?_⟩
      have h0 : (0:ℝ) ≤ 1 / √(4 - dhi ^ 2) := by positivity
      exact fx_nonneg_iff.mp (le_trans h0 hle)
    · simp only [hf, decide_false, Bool.false_eq_true, ite_false, hc1, fx_zero, le_refl, and_self]
  -- μ-bound
  have hmu : (if first i j then 0 else 2 * Real.arcsin (min dhi 2 / 2) - 2 * Real.arcsin (dlo / 2)) ≤ fx c0 := by
    rw [hfst]
    by_cases hf : d2mx < thr198
    · simp only [hf, decide_true, ite_true, hc0, fx_zero, le_refl]
    · simp only [hf, decide_false, Bool.false_eq_true, ite_false, hc0]
      have hup : Real.arcsin (min dhi 2 / 2) ≤ fx up := by
        rw [hup]
        split_ifs with h4
        · have hdhiI : ivMem dhi ((Iv.pt d2mx).div2e PR).sqrt := by
            apply Iv.mem_sqrt; rw [hmax]; exact mem_d2I d2mx
          have h1 := ivMem_hi_le hdhiI
          have h2 := le_shrU (((Iv.pt d2mx).div2e PR).sqrt.hi) 1
          have hx : min dhi 2 / 2 ≤ fx (shrU ((Iv.pt d2mx).div2e PR).sqrt.hi 1) := by
            have : dhi / 2 ≤ fx (shrU ((Iv.pt d2mx).div2e PR).sqrt.hi 1) := by
              unfold fx at h1 ⊢
              calc dhi / 2 ≤ (((Iv.pt d2mx).div2e PR).sqrt.hi : ℝ) / 2 ^ PR / 2 := by linarith
                _ = (((Iv.pt d2mx).div2e PR).sqrt.hi : ℝ) / 2 ^ 1 / 2 ^ PR := by ring
                _ ≤ _ := by gcongr
            exact le_trans (by gcongr; exact min_le_left _ _) this
          exact le_trans (Real.arcsin_le_arcsin hx) (asinHi_sound cs hcs asinC _)
        · have h1 := le_shrU piHi 1
          have h2 := le_piHi
          have : π / 2 ≤ fx (shrU piHi 1) := by
            unfold fx at h2 ⊢
            calc π / 2 ≤ (piHi : ℝ) / 2 ^ PR / 2 := by linarith
              _ = (piHi : ℝ) / 2 ^ 1 / 2 ^ PR := by ring
              _ ≤ _ := by gcongr
          exact le_trans (Real.arcsin_le_pi_div_two _) this
      have hlw : fx lw ≤ Real.arcsin (dlo / 2) := by
        have hx0 : 0 ≤ fx (shrD dmn.lo 1) := by
          apply fx_nonneg_iff.mpr; unfold shrD
          rw [Int.shiftRight_eq_div_pow]
          exact Int.ediv_nonneg (le_of_lt hdmnpos) (by positivity)
        have h1 := asinLo_sound cs hcs asinC (shrD dmn.lo 1) hx0
        have h2 : fx (shrD dmn.lo 1) ≤ dlo / 2 := by
          have h3 := shrD_le dmn.lo 1
          have h4 := ivMem_lo_le hdmnI
          unfold fx at h4 ⊢
          calc ((shrD dmn.lo 1 : ℤ) : ℝ) / 2 ^ PR ≤ ((dmn.lo : ℝ) / 2 ^ 1) / 2 ^ PR := by gcongr
            _ = (dmn.lo : ℝ) / 2 ^ PR / 2 := by ring
            _ ≤ dlo / 2 := by linarith
        exact le_trans h1 (Real.arcsin_le_arcsin h2)
      have : fx (2 * (up - lw)) = 2 * (fx up - fx lw) := by unfold fx; push_cast; ring
      rw [this]; linarith
  -- tcap bound
  have htc : min (((R i).eps + (R j).eps) / dlo) π ≤ fx tcap := by
    have hq := Iv.mem_div hdlI hdmnI hdmnpos
    have h1 := ivMem_hi_le hq
    have h2 := le_piHi
    rw [htcap]
    unfold fx at h1 h2 ⊢
    push_cast
    rw [← min_div_div_right (by positivity)]
    exact min_le_min h1 h2
  -- the motion bound
  have hmot : Tseg dlo dhi (first i j) ((R i).eps + (R j).eps) ≤ fx motion :=
    Tseg_le_motion hdlI hlam.2 hlam.1 hmu htc heps0
  have hTb : Tbound (R i) (R j) (first i j) ((R i).eps + (R j).eps) ≤ fx motion := by
    rw [VertexRect.Tbound_eq_Tseg]; exact hmot
  have hnu : nuCount R first i j ≤ nvc := nuCount_le_nvCount hk hv first i j hdeli hTb
  have hν0 : 0 ≤ ν := Nat.cast_nonneg _
  have hνn : ν ≤ (nvc : ℝ) := by show ((nuCount R first i j : ℕ) : ℝ) ≤ (nvc : ℝ); exact_mod_cast hnu
  by_cases hz : (nvc == 0) = true
  · rw [if_pos hz] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨h0, ha, hb, hc⟩ := h
    subst h0 ha hb hc
    have hn0 : nvc = 0 := by simpa using hz
    have hν : ν = 0 := by
      have : nuCount R first i j = 0 := by omega
      show ((nuCount R first i j : ℕ) : ℝ) = 0
      rw [this]; simp
    rw [hν]; simp
  · rw [if_neg hz] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨h0, ha, hb, hc⟩ := h
    subst h0 ha hb hc
    -- nonnegativity
    have hdd : dlo ≤ dhi := Real.sqrt_le_sqrt (dminSq_le_dmaxSq_box hk hv i j)
    have harc : 2 * Real.arcsin (dlo / 2) ≤ 2 * Real.arcsin (min dhi 2 / 2) := by
      have : dlo / 2 ≤ min dhi 2 / 2 := by gcongr; exact le_min hdd hdlo.le
      have := Real.arcsin_le_arcsin this; linarith
    have hlam0 : 0 ≤ lamT dhi (first i j) := by unfold lamT; split_ifs <;> positivity
    have hmu0 : 0 ≤ muT dlo dhi (first i j) := by unfold muT; split_ifs <;> linarith
    have hL : lamT dhi (first i j) ≤ fx c1 := hlam.1
    have hM : muT dlo dhi (first i j) ≤ fx c0 := hmu
    have hc10 : 0 ≤ fx c1 := le_trans hlam0 hL
    have hc00 : 0 ≤ fx c0 := le_trans hmu0 hM
    have hT0 : 0 ≤ Tseg dlo dhi (first i j) ((R i).eps + (R j).eps) := by
      unfold Tseg
      have h1 : 0 ≤ min (((R i).eps + (R j).eps) / dlo) π := le_min (by positivity) Real.pi_pos.le
      have h2 : 0 ≤ (if first i j then ((R i).eps + (R j).eps) / √(4 - dhi ^ 2)
          else 2 * Real.arcsin (min dhi 2 / 2) - 2 * Real.arcsin (dlo / 2)) := by
        split_ifs
        · positivity
        · linarith
      linarith
    have hE1 : 0 ≤ E1 := by positivity
    have hE2 : 0 ≤ E2 := by
      have := m2pt_nonneg (σ i); have := m2pt_nonneg (σ j); positivity
    have hE4 : 0 ≤ E4 := by
      have := m4pt_nonneg (σ i); have := m4pt_nonneg (σ j); positivity
    -- enclosures of the sums
    have hS1 : ivMem E1 (m1i.add m1j) := Iv.mem_add hm1i hm1j
    have hS2 : ivMem E2 ((m2i.add m2j).add ((m1i.mul m1j).mulNat 2)) := by
      have := Iv.mem_add (Iv.mem_add hm2i hm2j) (Iv.mem_mulNat (Iv.mem_mul hm1i hm1j) 2)
      show ivMem (m2pt (σ i) + m2pt (σ j) + 2 * √(m2pt (σ i)) * √(m2pt (σ j))) _
      convert this using 1; push_cast; ring
    have hS4 : ivMem E4 ((m4i.add m4j).mulNat 8) := by
      have := Iv.mem_mulNat (Iv.mem_add hm4i hm4j) 8
      show ivMem (8 * (m4pt (σ i) + m4pt (σ j))) _
      convert this using 1; push_cast; ring
    have hS1h := ivMem_hi_le hS1
    have hS2h := ivMem_hi_le hS2
    have hS4h := ivMem_hi_le hS4
    refine ⟨?_, ?_, ?_⟩
    · -- the motion term
      rw [mul_assoc]
      apply count_mul_le hν0 hνn (mul_nonneg heps0 hT0)
      have hε := ivMem_hi_le hdlI
      calc ((R i).eps + (R j).eps) * Tseg dlo dhi (first i j) ((R i).eps + (R j).eps)
          ≤ fx dl.hi * fx motion := mul_le_mul hε hmot hT0 (le_trans heps0 hε)
        _ ≤ _ := fx_mul_le_shrU _ _
    · -- the first moment term
      apply count_mul_le hν0 hνn
      · have : 0 ≤ min (E2 / dlo) (π * E1) := le_min (by positivity) (by positivity)
        positivity
      rw [fx_add', fx_add', fx_min']
      have t1 : lamT dhi (first i j) * E2 ≤ fx (shrU (c1 * ((m2i.add m2j).add ((m1i.mul m1j).mulNat 2)).hi) PR) :=
        le_trans (mul_le_mul hL hS2h hE2 hc10) (fx_mul_le_shrU _ _)
      have t2 : muT dlo dhi (first i j) * E1 ≤ fx (shrU (c0 * (m1i.add m1j).hi) PR) :=
        le_trans (mul_le_mul hM hS1h hE1 hc00) (fx_mul_le_shrU _ _)
      have t3 : min (E2 / dlo) (π * E1) ≤ min (fx (((m2i.add m2j).add ((m1i.mul m1j).mulNat 2)).div dmn).hi)
          (fx (piIv.mul (m1i.add m1j)).hi) :=
        min_le_min (ivMem_hi_le (Iv.mem_div hS2 hdmnI hdmnpos)) (ivMem_hi_le (Iv.mem_mul ivMem_pi hS1))
      linarith
    · -- the second moment term
      apply count_mul_le hν0 hνn (Real.sqrt_nonneg _)
      have hL2 : lamT dhi (first i j) ^ 2 ≤ fx (shrU (c1 * c1) PR) := by
        rw [sq]; exact le_trans (mul_le_mul hL hL hlam0 hc10) (fx_mul_le_shrU _ _)
      have hM2 : muT dlo dhi (first i j) ^ 2 ≤ fx (shrU (c0 * c0) PR) := by
        rw [sq]; exact le_trans (mul_le_mul hM hM hmu0 hc00) (fx_mul_le_shrU _ _)
      have t1 : lamT dhi (first i j) ^ 2 * E4 ≤
          fx (shrU (shrU (c1 * c1) PR * ((m4i.add m4j).mulNat 8).hi) PR) :=
        le_trans (mul_le_mul hL2 hS4h hE4 (le_trans (sq_nonneg _) hL2)) (fx_mul_le_shrU _ _)
      have t2 : muT dlo dhi (first i j) ^ 2 * E2 ≤
          fx (shrU (shrU (c0 * c0) PR * ((m2i.add m2j).add ((m1i.mul m1j).mulNat 2)).hi) PR) :=
        le_trans (mul_le_mul hM2 hS2h hE2 (le_trans (sq_nonneg _) hM2)) (fx_mul_le_shrU _ _)
      have hdlo2 : dlo ^ 2 = dminSq (R i) (R j) := Real.sq_sqrt (VertexRect.dminSq_nonneg _ _)
      have t3 : min (E4 / dlo ^ 2) (π ^ 2 * E2) ≤ min (fx (((m4i.add m4j).mulNat 8).div d2mnI).hi)
          (fx (piIv.sqr.mul ((m2i.add m2j).add ((m1i.mul m1j).mulNat 2))).hi) := by
        rw [hdlo2]
        exact min_le_min (ivMem_hi_le (Iv.mem_div hS4 hd2I hd2Ipos))
          (ivMem_hi_le (Iv.mem_mul (Iv.mem_sqr ivMem_pi) hS2))
      have hsq := ivMem_hi_le (Iv.mem_sqrt (Iv.mem_pt (3 *
                (shrU (shrU (c1 * c1) PR * ((m4i.add m4j).mulNat 8).hi) PR +
                    shrU (shrU (c0 * c0) PR * ((m2i.add m2j).add ((m1i.mul m1j).mulNat 2)).hi) PR +
                  min (((m4i.add m4j).mulNat 8).div d2mnI).hi
                    (piIv.sqr.mul ((m2i.add m2j).add ((m1i.mul m1j).mulNat 2))).hi))))
      refine le_trans (Real.sqrt_le_sqrt ?_) hsq
      have e3 : ∀ z : ℤ, fx (3 * z) = 3 * fx z := fun z => by unfold fx; push_cast; ring
      rw [e3, fx_add', fx_add', fx_min']
      linarith
