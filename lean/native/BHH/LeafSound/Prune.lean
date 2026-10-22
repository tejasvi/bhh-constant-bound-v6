/-
Module D, part 5: the code's vertex count `nvCount` is at least the real `nuCount` of the vertex lemma (pruning test of
Remark 3.2 with upper bounds).
-/
import BHH.LeafSound.RemGlue

open BHH.Cert Real

noncomputable section

namespace BHH

lemma sqrt_div_eq_sqrt_inv_sq {d : ℝ} (hd : 0 < d) : √(1 - d ^ 2 / 4) / d = √(1 / d ^ 2 - 1 / 4) := by
  rw [show 1 / d ^ 2 - 1 / 4 = (1 - d ^ 2 / 4) / d ^ 2 by field_simp]
  rw [Real.sqrt_div' _ (by positivity), Real.sqrt_sq hd.le]

/-- the vertex of the code's pruning test encloses the real vertex -/
lemma mem_vertex {ax ay bx' by' : ℤ} (hdc : 0 < (bx' - ax) ^ 2 + (by' - ay) ^ 2)
    (hI : 0 < (Iv.div2e (Iv.pt ((bx' - ax) * (bx' - ax) + (by' - ay) * (by' - ay))) PR).lo) :
    let a : Pt := (fx ax, fx ay)
    let b : Pt := (fx bx', fx by')
    let wx := bx' - ax
    let wy := by' - ay
    let dc2I := Iv.div2e (Iv.pt (wx * wx + wy * wy)) PR
    let sIv := Iv.sqrt (Iv.sub (Iv.div (Iv.int 1) dc2I) (Iv.div2e (Iv.int 1) 2))
    let mx := Iv.add (Iv.pt ax) (Iv.div2e (Iv.pt wx) 1)
    let my := Iv.add (Iv.pt ay) (Iv.div2e (Iv.pt wy) 1)
    let ox := Iv.mul sIv (Iv.pt (-wy))
    let oy := Iv.mul sIv (Iv.pt wx)
    ivMem (vertexPts a b).1.1 (Iv.add mx ox) ∧ ivMem (vertexPts a b).1.2 (Iv.add my oy) ∧
    ivMem (vertexPts a b).2.1 (Iv.sub mx ox) ∧ ivMem (vertexPts a b).2.2 (Iv.sub my oy) := by
  intro a b wx wy dc2I sIv mx my ox oy
  -- real quantities
  have hw1 : (b - a).1 = fx wx := by simp [a, b, wx, fx_sub]
  have hw2 : (b - a).2 = fx wy := by simp [a, b, wy, fx_sub]
  have hdc2 : enorm2 (b - a) ^ 2 = ((wx * wx + wy * wy : ℤ) : ℝ) / (2 : ℝ) ^ (2 * PR) := by
    unfold enorm2; rw [Real.sq_sqrt (by positivity), hw1, hw2]
    unfold fx; push_cast; rw [pow_mul']; field_simp
  have hdcpos : 0 < enorm2 (b - a) := by
    have : (0:ℝ) < ((wx * wx + wy * wy : ℤ) : ℝ) / (2 : ℝ) ^ (2 * PR) := by
      apply div_pos _ (by positivity); push_cast
      have : (0:ℤ) < wx * wx + wy * wy := by nlinarith
      exact_mod_cast this
    rw [← hdc2] at this
    exact lt_of_le_of_ne (by unfold enorm2; positivity) (fun h => by rw [← h] at this; simp at this)
  have hd2 : ivMem (enorm2 (b - a) ^ 2) dc2I := by rw [hdc2]; exact mem_d2I _
  have hinv := Iv.mem_div (Iv.mem_int 1) hd2 hI
  have hq := Iv.mem_div2e (Iv.mem_int 1) 2
  have hs := Iv.mem_sqrt (Iv.mem_sub hinv hq)
  have hs' : ivMem (√(1 - enorm2 (b - a) ^ 2 / 4) / enorm2 (b - a)) sIv := by
    rw [sqrt_div_eq_sqrt_inv_sq hdcpos]
    convert hs using 2; push_cast; ring
  have hmx : ivMem (a.1 + (1 / 2 : ℝ) * (b - a).1) mx := by
    have := Iv.mem_add (Iv.mem_pt ax) (Iv.mem_div2e (Iv.mem_pt wx) 1)
    rw [hw1]; convert this using 1; simp [a]; ring
  have hmy : ivMem (a.2 + (1 / 2 : ℝ) * (b - a).2) my := by
    have := Iv.mem_add (Iv.mem_pt ay) (Iv.mem_div2e (Iv.mem_pt wy) 1)
    rw [hw2]; convert this using 1; simp [a]; ring
  have hox : ivMem (√(1 - enorm2 (b - a) ^ 2 / 4) / enorm2 (b - a) * (-(b - a).2)) ox := by
    have := Iv.mem_mul hs' (Iv.mem_pt (-wy))
    rw [hw2]; convert this using 2; unfold fx; push_cast; ring
  have hoy : ivMem (√(1 - enorm2 (b - a) ^ 2 / 4) / enorm2 (b - a) * (b - a).1) oy := by
    have := Iv.mem_mul hs' (Iv.mem_pt wx)
    rw [hw1]; exact this
  unfold vertexPts
  simp only [Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := Iv.mem_add hmx hox; convert this using 1
  · have := Iv.mem_add hmy hoy; convert this using 1
  · have := Iv.mem_sub hmx hox; convert this using 1
  · have := Iv.mem_sub hmy hoy; convert this using 1

/-- `fx` of the code's shifted square bound: `fx (shrD (R0 * R0) PR) ≤ (fx R0)^2` -/
lemma fx_shrD_sq_le (R0 : ℤ) : fx (shrD (R0 * R0) PR) ≤ fx R0 ^ 2 := by
  have h := shrD_le (R0 * R0) PR
  unfold fx
  calc ((shrD (R0 * R0) PR : ℤ) : ℝ) / 2 ^ PR ≤ ((R0 * R0 : ℤ) : ℝ) / 2 ^ PR / 2 ^ PR := by gcongr
    _ = ((R0 : ℝ) / 2 ^ PR) ^ 2 := by push_cast; ring

/-- the pruning test of the code certifies coverage in the sense of Remark 3.2 -/
lemma certCovered_of_code {k : ℕ} (hk : 3 ≤ k) {lo hi : List ℤ} (hv : ValidBox k lo hi)
    (first : Fin k → Fin k → Bool) (i j : Fin k) {deli : Iv} {motion : ℤ}
    (hdeli : ivMem (boxRects k lo hi i).eps deli)
    (hmot : Tbound (boxRects k lo hi i) (boxRects k lo hi j) (first i j)
      ((boxRects k lo hi i).eps + (boxRects k lo hi j).eps) ≤ fx motion)
    {P : Pt} {px py : Iv} (hpx : ivMem P.1 px) (hpy : ivMem P.2 py)
    (h : vertexCovered (ptBoxes k lo hi) ((ptBoxes k lo hi).map moments) i.val j.val deli motion px py = true) :
    certCovered (boxRects k lo hi) first i j P := by
  unfold vertexCovered at h
  rw [List.any_eq_true] at h
  obtain ⟨l, hl, htest⟩ := h
  rw [List.mem_filter, List.mem_range] at hl
  obtain ⟨hlk, hlij⟩ := hl
  have hlen : (ptBoxes k lo hi).length = k := by simp [ptBoxes]
  rw [hlen] at hlk
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hlij
  refine ⟨⟨l, hlk⟩, fun h' => hlij.1 (by simp [← h']), fun h' => hlij.2 (by simp [← h']), ?_⟩
  simp only at htest
  split_ifs at htest with hR0
  set Pl := (ptBoxes k lo hi).getD l default
  -- ε_l enclosure
  have hl' : l < (ptBoxes k lo hi).length := by simp [ptBoxes]; exact hlk
  have hmoml : ((ptBoxes k lo hi).map moments).getD l default = moments Pl := by
    rw [List.getD_eq_getElem _ _ (by simp [ptBoxes]; exact hlk), List.getElem_map]
    simp only [Pl, List.getD, List.getElem?_eq_getElem hl', Option.getD_some]
  rw [hmoml] at htest hR0
  have htest' := of_decide_eq_true htest
  obtain ⟨hevx, hevy⟩ := ptBoxes_even hk hv ⟨l, hlk⟩
  have hdell := (moments_sound hevx hevy).1
  -- centre of l
  have hcl : (boxRects k lo hi ⟨l, hlk⟩).centre = (fx Pl.xc, fx Pl.yc) := centre_rectOf _ hevx hevy
  -- distance bound
  have hdx := Iv.mem_sub hpx (Iv.mem_pt Pl.xc)
  have hdy := Iv.mem_sub hpy (Iv.mem_pt Pl.yc)
  have hd2 := Iv.mem_add (Iv.mem_sqr hdx) (Iv.mem_sqr hdy)
  set R0 := ONE - ((deli.hi + motion) + (moments Pl).1.hi) with hR0def
  have hdist : sqDist P (fx Pl.xc, fx Pl.yc) < fx R0 ^ 2 := by
    have h1 : sqDist P (fx Pl.xc, fx Pl.yc) ≤ fx (Iv.add (Iv.sqr (Iv.sub px (Iv.pt Pl.xc)))
        (Iv.sqr (Iv.sub py (Iv.pt Pl.yc)))).hi := by
      have := ivMem_hi_le hd2; unfold sqDist; simpa using this
    have h3 : fx (Iv.add (Iv.sqr (Iv.sub px (Iv.pt Pl.xc))) (Iv.sqr (Iv.sub py (Iv.pt Pl.yc)))).hi
        < fx (shrD (R0 * R0) PR) := by
      unfold fx; rw [div_lt_div_iff_of_pos_right (by positivity)]; exact_mod_cast htest'
    exact lt_of_le_of_lt h1 (lt_of_lt_of_le h3 (fx_shrD_sq_le R0))
  have hR0pos : 0 < fx R0 := fx_pos_iff.mpr (lt_of_not_ge hR0)
  have hedist : edist2 P (fx Pl.xc, fx Pl.yc) < fx R0 := by
    unfold edist2
    rw [Real.sqrt_lt' hR0pos]; exact hdist
  rw [hcl]
  have hfxR0 : fx R0 = 1 - (fx deli.hi + fx motion + fx (moments Pl).1.hi) := by
    rw [hR0def]; unfold fx; push_cast; rw [ONE_cast]; unfold SC; field_simp
  have hei := ivMem_hi_le hdeli
  have hel := ivMem_hi_le hdell
  have hRl : (boxRects k lo hi ⟨l, hlk⟩).eps = (rectOf Pl).eps := rfl
  rw [hRl]
  linarith

lemma ite01_le {p q : Prop} [Decidable p] [Decidable q] (h : q → p) :
    (if p then 0 else 1 : ℕ) ≤ (if q then 0 else 1 : ℕ) := by
  by_cases hq : q
  · simp [h hq, hq]
  · simp only [hq, ite_false]; split_ifs <;> omega

lemma nuCount_le_two {k : ℕ} (R : Fin k → Rect) (first : Fin k → Fin k → Bool) (i j : Fin k) :
    nuCount R first i j ≤ 2 := by
  classical
  unfold nuCount; simp only
  split_ifs <;> omega

/-- the code's vertex count is an upper bound for `ν_ij` of the vertex lemma -/
theorem nuCount_le_nvCount {k : ℕ} (hk : 3 ≤ k) {lo hi : List ℤ} (hv : ValidBox k lo hi)
    (first : Fin k → Fin k → Bool) (i j : Fin k) {deli : Iv} {motion : ℤ}
    (hdeli : ivMem (boxRects k lo hi i).eps deli)
    (hmot : Tbound (boxRects k lo hi i) (boxRects k lo hi j) (first i j)
      ((boxRects k lo hi i).eps + (boxRects k lo hi j).eps) ≤ fx motion) :
    nuCount (boxRects k lo hi) first i j ≤
      nvCount (ptBoxes k lo hi) ((ptBoxes k lo hi).map moments) i.val j.val deli motion := by
  classical
  unfold nvCount
  dsimp only
  set Pi := (ptBoxes k lo hi).getD i.val default with hPi
  set Pj := (ptBoxes k lo hi).getD j.val default with hPj
  obtain ⟨hix, hiy⟩ := ptBoxes_even hk hv i
  obtain ⟨hjx, hjy⟩ := ptBoxes_even hk hv j
  have hci : (boxRects k lo hi i).centre = (fx Pi.xc, fx Pi.yc) := centre_rectOf _ hix hiy
  have hcj : (boxRects k lo hi j).centre = (fx Pj.xc, fx Pj.yc) := centre_rectOf _ hjx hjy
  set wx := Pj.xc - Pi.xc with hwx
  set wy := Pj.yc - Pi.yc with hwy
  have hdc : edist2 (boxRects k lo hi i).centre (boxRects k lo hi j).centre
      = √(((wx * wx + wy * wy : ℤ) : ℝ) / (2 : ℝ) ^ (2 * PR)) := by
    rw [hci, hcj]; unfold edist2 sqDist; congr 1
    simp only [hwx, hwy]; unfold fx; push_cast; rw [pow_mul']; field_simp; ring
  by_cases hc : 0 < wx * wx + wy * wy ∧ wx * wx + wy * wy < 4 * ONE * ONE ∧
      0 < (Iv.div2e (Iv.pt (wx * wx + wy * wy)) PR).lo
  · rw [if_pos hc]
    obtain ⟨h0, h4, hI⟩ := hc
    -- the real condition holds
    have hreal : 0 < edist2 (boxRects k lo hi i).centre (boxRects k lo hi j).centre ∧
        edist2 (boxRects k lo hi i).centre (boxRects k lo hi j).centre < 2 := by
      rw [hdc]
      have hpos : (0:ℝ) < ((wx * wx + wy * wy : ℤ) : ℝ) / (2 : ℝ) ^ (2 * PR) := by
        apply div_pos _ (by positivity); exact_mod_cast h0
      have hlt : ((wx * wx + wy * wy : ℤ) : ℝ) / (2 : ℝ) ^ (2 * PR) < 4 := by
        rw [← ONE_sq4_cast]; gcongr
      refine ⟨Real.sqrt_pos.mpr hpos, ?_⟩
      rw [Real.sqrt_lt' (by norm_num : (0:ℝ) < 2)]
      linarith
    unfold nuCount
    simp only
    rw [if_pos hreal]
    have hpos : 0 < (Pj.xc - Pi.xc) ^ 2 + (Pj.yc - Pi.yc) ^ 2 := by nlinarith
    obtain ⟨v1x, v1y, v2x, v2y⟩ := mem_vertex (ax := Pi.xc) (ay := Pi.yc) (bx' := Pj.xc) (by' := Pj.yc) hpos hI
    rw [hci, hcj]
    have hcov := fun (P : Pt) (px py : Iv) (hpx : ivMem P.1 px) (hpy : ivMem P.2 py)
        (h : vertexCovered (ptBoxes k lo hi) ((ptBoxes k lo hi).map moments) i.val j.val deli motion px py = true) =>
      certCovered_of_code hk hv first i j hdeli hmot hpx hpy h
    exact Nat.add_le_add (ite01_le (fun h => hcov _ _ _ v1x v1y h)) (ite01_le (fun h => hcov _ _ _ v2x v2y h))
  · rw [if_neg hc]
    exact nuCount_le_two _ _ _ _

end BHH
