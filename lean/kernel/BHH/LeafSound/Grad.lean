/-
Module D, part 10: the gradient of the union area in box coordinates, its code enclosure, and the bounds `sumb`, `Sb`.
-/
import BHH.LeafSound.Pointwise
import BHH.LeafSound.LeafAlt

open BHH.Cert Real MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace BHH

/-- the gradient `∇A` at the centres in box coordinates `x = (r_2, ξ_2, η_2, ...)` -/
def gradBox (k : ℕ) (g : Fin k → Pt) (d : Fin (mDim k)) : ℝ :=
  if d.val = 0 then (ptN g 1).1
  else if d.val % 2 = 1 then (ptN g ((d.val + 3) / 2)).1 else (ptN g ((d.val + 2) / 2)).2

lemma grad_identity3 (g : Fin 3 → Pt) (x cx : Fin (mDim 3) → ℝ) :
    ∑ i, ((g i).1 * (xcfg 3 x i - xcfg 3 cx i).1 + (g i).2 * (xcfg 3 x i - xcfg 3 cx i).2) =
      ∑ d, gradBox 3 g d * (x d - cx d) := by
  show ∑ i : Fin 3, _ = ∑ d : Fin 3, _
  simp [Fin.sum_univ_succ, xcfg, xget, gradBox, ptN, mDim]

lemma grad_identity4 (g : Fin 4 → Pt) (x cx : Fin (mDim 4) → ℝ) :
    ∑ i, ((g i).1 * (xcfg 4 x i - xcfg 4 cx i).1 + (g i).2 * (xcfg 4 x i - xcfg 4 cx i).2) =
      ∑ d, gradBox 4 g d * (x d - cx d) := by
  show ∑ i : Fin 4, _ = ∑ d : Fin 5, _
  simp [Fin.sum_univ_succ, xcfg, xget, gradBox, ptN, mDim]
  ring

lemma grad_identity5 (g : Fin 5 → Pt) (x cx : Fin (mDim 5) → ℝ) :
    ∑ i, ((g i).1 * (xcfg 5 x i - xcfg 5 cx i).1 + (g i).2 * (xcfg 5 x i - xcfg 5 cx i).2) =
      ∑ d, gradBox 5 g d * (x d - cx d) := by
  show ∑ i : Fin 5, _ = ∑ d : Fin 7, _
  simp [Fin.sum_univ_succ, xcfg, xget, gradBox, ptN, mDim]
  ring

/-- `Σ_i ⟨g_i, y_i - c_i⟩ = Σ_d b_d (x_d - c_d)` in box coordinates (k = 3, 4, 5) -/
lemma grad_identity {k : ℕ} (hk : 3 ≤ k) (hk5 : k ≤ 5) (g : Fin k → Pt) (x cx : Fin (mDim k) → ℝ) :
    ∑ i, ((g i).1 * (xcfg k x i - xcfg k cx i).1 + (g i).2 * (xcfg k x i - xcfg k cx i).2) =
      ∑ d, gradBox k g d * (x d - cx d) := by
  interval_cases k
  · exact grad_identity3 g x cx
  · exact grad_identity4 g x cx
  · exact grad_identity5 g x cx

lemma gradList_getD (k : ℕ) (u : UnionRes) {d : ℕ} (hd : d < 2 * k - 3) :
    (gradList k u).getD d default = (if d == 0 then u.gx.getD 1 default
      else if d % 2 == 1 then u.gx.getD ((d + 3) / 2) default else u.gy.getD ((d + 2) / 2) default) := by
  unfold gradList
  rw [List.getD_eq_getElem _ _ (by simpa using hd)]
  simp

lemma widthList_getD (k : ℕ) (lo hi : List ℤ) {d : ℕ} (hd : d < 2 * k - 3) :
    (widthList k lo hi).getD d 0 = listGet hi d - listGet lo d := by
  unfold widthList
  rw [List.getD_eq_getElem _ _ (by simpa using hd)]
  simp

/-- the code's gradient list encloses the gradient in box coordinates -/
lemma mem_gradList {k : ℕ} (hk : 3 ≤ k) {g : Fin k → Pt} {u : UnionRes}
    (hg : ∀ i : Fin k, ivMem (g i).1 (u.gx.getD i.val default) ∧ ivMem (g i).2 (u.gy.getD i.val default))
    (d : Fin (mDim k)) : ivMem (gradBox k g d) ((gradList k u).getD d.val default) := by
  have hd := d.isLt
  have hm : mDim k = 2 * k - 3 := rfl
  rw [gradList_getD k u (by rw [← hm]; exact hd)]
  unfold gradBox ptN
  by_cases h0 : d.val = 0
  · have h1 : 1 < k := by omega
    simp only [h0, beq_self_eq_true, ite_true, dif_pos h1]
    exact (hg ⟨1, h1⟩).1
  · by_cases h1 : d.val % 2 = 1
    · have hi : (d.val + 3) / 2 < k := by omega
      have h0' : (d.val == 0) = false := by simpa using h0
      simp only [h0, h1, h0', beq_self_eq_true, ite_true, ite_false, dif_pos hi, Bool.false_eq_true]
      exact (hg ⟨(d.val + 3) / 2, hi⟩).1
    · have hi : (d.val + 2) / 2 < k := by omega
      have h0' : (d.val == 0) = false := by simpa using h0
      have h1' : (d.val % 2 == 1) = false := by simpa using h1
      simp only [h0, h1, h0', h1', ite_false, dif_pos hi, Bool.false_eq_true]
      exact (hg ⟨(d.val + 2) / 2, hi⟩).2

lemma foldl_add_sum {α : Type*} (t : α → ℤ) (l : List α) (a : ℤ) :
    l.foldl (fun acc x => acc + t x) a = a + (l.map t).sum := by
  induction l generalizing a with
  | nil => simp
  | cons x l ih => simp only [List.foldl, ih, List.map_cons, List.sum_cons]; ring

lemma zip_range_sum {α β : Type*} (m : ℕ) (f : ℕ → α) (g : ℕ → β) (t : α × β → ℤ) :
    ((((List.range m).map f).zip ((List.range m).map g)).map t).sum = ∑ d : Fin m, t (f d.val, g d.val) := by
  rw [List.zip_map', List.map_map, ← Finset.sum_range (fun d => t (f d, g d)), Finset.sum_eq_multiset_sum]
  simp only [Finset.range_val, Multiset.range, Multiset.map_coe, Multiset.sum_coe]
  rfl

lemma ediv_add_one_ge (S : ℤ) {n : ℤ} (hn : 0 < n) : (S : ℝ) / n ≤ ((S / n + 1 : ℤ) : ℝ) := by
  have h := Int.lt_ediv_add_one_mul_self S hn
  have h' : (S : ℝ) < ((S / n + 1 : ℤ) : ℝ) * n := by exact_mod_cast h
  rw [div_le_iff₀ (by exact_mod_cast hn)]
  linarith

/-- `Σ_d |b_d| w_d / 2 ≤ fx sumb` -/
lemma sumAbs_ge {k : ℕ} (hk : 3 ≤ k) {g : Fin k → Pt} {u : UnionRes}
    (hg : ∀ i : Fin k, ivMem (g i).1 (u.gx.getD i.val default) ∧ ivMem (g i).2 (u.gy.getD i.val default))
    (lo hi : List ℤ) :
    ∑ d : Fin (mDim k), |gradBox k g d| * (realLo k hi d - realLo k lo d) / 2 ≤
      fx (sumAbs (gradList k u) (widthList k lo hi)) := by
  have hm : mDim k = 2 * k - 3 := rfl
  have e : sumAbs (gradList k u) (widthList k lo hi) =
      (((gradList k u).zip (widthList k lo hi)).map (fun bh => (Iv.mul (Iv.abs bh.1) (Iv.pt bh.2)).hi)).sum / 2
        + 1 := by
    unfold sumAbs; rw [← zero_add (List.sum _), ← foldl_add_sum]
  rw [e]
  have e2 : (((gradList k u).zip (widthList k lo hi)).map (fun bh => (Iv.mul (Iv.abs bh.1) (Iv.pt bh.2)).hi)).sum
      = ∑ d : Fin (mDim k), (Iv.mul (Iv.abs ((gradList k u).getD d.val default))
          (Iv.pt ((widthList k lo hi).getD d.val 0))).hi := by
    conv_lhs => unfold gradList widthList
    rw [zip_range_sum]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    rw [gradList_getD k u (by simp [hm]), widthList_getD k lo hi (by simp [hm])]
  rw [e2]
  have key : ∀ d : Fin (mDim k), |gradBox k g d| * (realLo k hi d - realLo k lo d) ≤
      fx (Iv.mul (Iv.abs ((gradList k u).getD d.val default)) (Iv.pt ((widthList k lo hi).getD d.val 0))).hi := by
    intro d
    have hm' := Iv.mem_mul (Iv.mem_abs (mem_gradList hk hg d)) (Iv.mem_pt ((widthList k lo hi).getD d.val 0))
    have := ivMem_hi_le hm'
    have hw : fx ((widthList k lo hi).getD d.val 0) = realLo k hi d - realLo k lo d := by
      rw [widthList_getD k lo hi (by rw [← hm]; exact d.isLt), fx_sub]; rfl
    rw [← hw]; exact this
  have hsum := Finset.sum_le_sum (fun d (_ : d ∈ Finset.univ) => key d)
  have h2 := ediv_add_one_ge (∑ d : Fin (mDim k), (Iv.mul (Iv.abs ((gradList k u).getD d.val default))
      (Iv.pt ((widthList k lo hi).getD d.val 0))).hi) (by norm_num : (0:ℤ) < 2)
  rw [← Finset.sum_div]
  have hfx : ∀ n : ℤ, fx n = (n : ℝ) / 2 ^ PR := fun n => rfl
  rw [hfx]
  calc (∑ d : Fin (mDim k), |gradBox k g d| * (realLo k hi d - realLo k lo d)) / 2
      ≤ (∑ d : Fin (mDim k), fx (Iv.mul (Iv.abs ((gradList k u).getD d.val default))
          (Iv.pt ((widthList k lo hi).getD d.val 0))).hi) / 2 := by gcongr
    _ = ((∑ d : Fin (mDim k), (Iv.mul (Iv.abs ((gradList k u).getD d.val default))
          (Iv.pt ((widthList k lo hi).getD d.val 0))).hi : ℤ) : ℝ) / ((2 : ℤ) : ℝ) / 2 ^ PR := by
        simp only [hfx, ← Finset.sum_div]; push_cast; ring
    _ ≤ _ := by gcongr

/-- `Σ_d b_d² w_d² / 12 ≤ fx Sb` -/
lemma sumSq_ge {k : ℕ} (hk : 3 ≤ k) {g : Fin k → Pt} {u : UnionRes}
    (hg : ∀ i : Fin k, ivMem (g i).1 (u.gx.getD i.val default) ∧ ivMem (g i).2 (u.gy.getD i.val default))
    (lo hi : List ℤ) :
    ∑ d : Fin (mDim k), gradBox k g d ^ 2 * (realLo k hi d - realLo k lo d) ^ 2 / 12 ≤
      fx (sumSq (gradList k u) (widthList k lo hi)) := by
  have hm : mDim k = 2 * k - 3 := rfl
  have e : sumSq (gradList k u) (widthList k lo hi) =
      (((gradList k u).zip (widthList k lo hi)).map (fun bh => (Iv.sqr (Iv.mul bh.1 (Iv.pt bh.2))).hi)).sum / 12
        + 1 := by
    unfold sumSq; rw [← zero_add (List.sum _), ← foldl_add_sum]
  rw [e]
  have e2 : (((gradList k u).zip (widthList k lo hi)).map (fun bh => (Iv.sqr (Iv.mul bh.1 (Iv.pt bh.2))).hi)).sum
      = ∑ d : Fin (mDim k), (Iv.sqr (Iv.mul ((gradList k u).getD d.val default)
          (Iv.pt ((widthList k lo hi).getD d.val 0)))).hi := by
    conv_lhs => unfold gradList widthList
    rw [zip_range_sum]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    rw [gradList_getD k u (by simp [hm]), widthList_getD k lo hi (by simp [hm])]
  rw [e2]
  have key : ∀ d : Fin (mDim k), gradBox k g d ^ 2 * (realLo k hi d - realLo k lo d) ^ 2 ≤
      fx (Iv.sqr (Iv.mul ((gradList k u).getD d.val default) (Iv.pt ((widthList k lo hi).getD d.val 0)))).hi := by
    intro d
    have hm' := Iv.mem_sqr (Iv.mem_mul (mem_gradList hk hg d) (Iv.mem_pt ((widthList k lo hi).getD d.val 0)))
    have := ivMem_hi_le hm'
    have hw : fx ((widthList k lo hi).getD d.val 0) = realLo k hi d - realLo k lo d := by
      rw [widthList_getD k lo hi (by rw [← hm]; exact d.isLt), fx_sub]; rfl
    rw [hw, mul_pow] at this; exact this
  have hsum := Finset.sum_le_sum (fun d (_ : d ∈ Finset.univ) => key d)
  have h2 := ediv_add_one_ge (∑ d : Fin (mDim k), (Iv.sqr (Iv.mul ((gradList k u).getD d.val default)
      (Iv.pt ((widthList k lo hi).getD d.val 0)))).hi) (by norm_num : (0:ℤ) < 12)
  rw [← Finset.sum_div]
  have hfx : ∀ n : ℤ, fx n = (n : ℝ) / 2 ^ PR := fun n => rfl
  rw [hfx]
  calc (∑ d : Fin (mDim k), gradBox k g d ^ 2 * (realLo k hi d - realLo k lo d) ^ 2) / 12
      ≤ (∑ d : Fin (mDim k), fx (Iv.sqr (Iv.mul ((gradList k u).getD d.val default)
          (Iv.pt ((widthList k lo hi).getD d.val 0)))).hi) / 12 := by gcongr
    _ = ((∑ d : Fin (mDim k), (Iv.sqr (Iv.mul ((gradList k u).getD d.val default)
          (Iv.pt ((widthList k lo hi).getD d.val 0)))).hi : ℤ) : ℝ) / ((12 : ℤ) : ℝ) / 2 ^ PR := by
        simp only [hfx, ← Finset.sum_div]; push_cast; ring
    _ ≤ _ := by gcongr

end BHH
