/-
Soundness of the sub-box shards of track K (`BHHCert/TreeCut.lean`), for every stream and every list of external
entries:
* `bnbCut_sound`: a cut tree whose external values are bounded by the integrals over the external boxes (`cutBoxes`,
  same preorder) is bounded by the integral over its box;
* `extOK_sound`: a passing external claim bounds the integral over its box (`bnbStream_sound`);
* `cutBox_sound`: one box from a passing `cutOK` and passing claims for all its entries;
* `extOK_of_chunks`: the claims of all entries from passing `subOK` checks of the chunks of the entry list.
-/
import BHH.TreeK
import BHHCert.TreeCut

open MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace BHH.KC

open BHH.Cert BHH.E

/-- the stream and the external values left over by `bnbCut` are those of `cutBoxes` -/
lemma bnbCut_rest {S : Type} (k : ℕ) (L : List ℤ → List ℤ → ℤ) (read : S → ℕ × S) :
    ∀ (fuel : ℕ) (s : S) (lo hi ext : List ℤ),
      (bnbCut k L read fuel s lo hi ext).2.1 = (cutBoxes read fuel s lo hi).2 ∧
      (bnbCut k L read fuel s lo hi ext).2.2 = ext.drop (cutBoxes read fuel s lo hi).1.length := by
  intro fuel
  induction fuel with
  | zero => intro s lo hi ext; simp [bnbCut, cutBoxes]
  | succ n ih =>
    intro s lo hi ext
    simp only [bnbCut, cutBoxes]
    by_cases h1 : (read s).1 = 1
    · simp [h1]
    by_cases h15 : (read s).1 = 15
    · simp [h15]
    by_cases h2 : 2 ≤ (read s).1
    · by_cases hd : (read s).1 - 2 < lo.length ∧ (read s).1 - 2 < hi.length
      · simp only [h1, h15, h2, hd, ite_false, ite_true, and_self]
        set d := (read s).1 - 2
        set mid := (lo.getD d 0 + hi.getD d 0) / 2
        obtain ⟨a1, a2⟩ := ih (read s).2 lo (hi.set d mid) ext
        set r1 := bnbCut k L read n (read s).2 lo (hi.set d mid) ext
        set B1 := cutBoxes read n (read s).2 lo (hi.set d mid)
        obtain ⟨b1, b2⟩ := ih r1.2.1 (lo.set d mid) hi r1.2.2
        refine ⟨?_, ?_⟩
        · rw [b1, a1]
        · rw [b2, a2, a1, List.drop_drop, List.length_append]
      · simp [h1, h15, h2, hd]
    · simp [h1, h15, h2]

/-- Soundness of the cut tree: if the `j`-th external value is bounded by the integral over the `j`-th external box
(for every `j`), the value is bounded by the integral over the box. -/
theorem bnbCut_sound {S : Type} {k : ℕ} {L : List ℤ → List ℤ → ℤ} (hL : LeafSoundProp k L)
    (read : S → ℕ × S) :
    ∀ (fuel : ℕ) (s : S) (lo hi ext : List ℤ), lo.length = mDim k →
      (∀ j < (cutBoxes read fuel s lo hi).1.length,
        ENNReal.ofReal (((ext.getD j 0 : ℤ) : ℝ) / 2 ^ OS) ≤
          ∫⁻ x in boxOf ((cutBoxes read fuel s lo hi).1.getD j ([], [])).1
            ((cutBoxes read fuel s lo hi).1.getD j ([], [])).2 ∩ Dk k, F2 k x) →
      ENNReal.ofReal (((bnbCut k L read fuel s lo hi ext).1 : ℝ) / 2 ^ OS) ≤
        ∫⁻ x in boxOf lo hi ∩ Dk k, F2 k x := by
  intro fuel
  induction fuel with
  | zero => intro s lo hi ext _ _; simp [bnbCut]
  | succ n ih =>
    intro s lo hi ext hl hext
    simp only [cutBoxes] at hext
    simp only [bnbCut]
    by_cases h1 : (read s).1 = 1
    · simp only [h1, ite_true]
      split_ifs with hv
      · exact ofReal_max_div_le (by positivity) (hL lo hi (validB_valid hv))
      · simp
    by_cases h15 : (read s).1 = 15
    · simp only [h15, ite_true] at hext ⊢
      have := hext 0 (by simp)
      rcases ext with _ | ⟨e, es⟩
      · simp
      · simpa using this
    by_cases h2 : 2 ≤ (read s).1
    swap
    · simp [h1, h15, h2]
    by_cases hd : (read s).1 - 2 < lo.length ∧ (read s).1 - 2 < hi.length
    swap
    · simp [h1, h15, h2, hd]
    simp only [h1, h15, h2, hd, ite_false, ite_true, and_self] at hext ⊢
    set d := (read s).1 - 2
    set mid := (lo.getD d 0 + hi.getD d 0) / 2
    obtain ⟨a1, a2⟩ := bnbCut_rest k L read n (read s).2 lo (hi.set d mid) ext
    have hl' : (lo.set d mid).length = mDim k := by simpa using hl
    -- the left half: external values `ext`, boxes of the left subtree
    have hA := ih (read s).2 lo (hi.set d mid) ext hl (fun j hj => by
      have := hext j (by rw [List.length_append]; omega)
      rwa [List.getD_append _ _ _ _ hj] at this)
    -- the right half: external values `ext.drop |left boxes|`, boxes of the right subtree
    have hB := ih (cutBoxes read n (read s).2 lo (hi.set d mid)).2 (lo.set d mid) hi
      (ext.drop (cutBoxes read n (read s).2 lo (hi.set d mid)).1.length) hl' (fun j hj => by
        have := hext ((cutBoxes read n (read s).2 lo (hi.set d mid)).1.length + j)
          (by rw [List.length_append]; omega)
        rw [List.getD_append_right _ _ _ _ (by omega), Nat.add_sub_cancel_left] at this
        simpa [List.getD_eq_getElem?_getD, List.getElem?_drop] using this)
    rw [← a2, ← a1] at hB
    set r1 := bnbCut k L read n (read s).2 lo (hi.set d mid) ext
    set r2 := bnbCut k L read n r1.2.1 (lo.set d mid) hi r1.2.2
    have hdm : d < mDim k := hl ▸ hd.1
    have hdisj := boxOf_halves_disjoint (m := mDim k) lo hi d mid hdm hd.1 hd.2
    calc ENNReal.ofReal (((r1.1 + r2.1 : ℤ) : ℝ) / 2 ^ OS)
        ≤ ENNReal.ofReal ((r1.1 : ℝ) / 2 ^ OS) + ENNReal.ofReal ((r2.1 : ℝ) / 2 ^ OS) := by
          rw [Int.cast_add, add_div]; exact ENNReal.ofReal_add_le
      _ ≤ (∫⁻ x in boxOf lo (hi.set d mid) ∩ Dk k, F2 k x) +
            ∫⁻ x in boxOf (lo.set d mid) hi ∩ Dk k, F2 k x := add_le_add hA hB
      _ = ∫⁻ x in (boxOf lo (hi.set d mid) ∩ Dk k) ∪ (boxOf (lo.set d mid) hi ∩ Dk k), F2 k x := by
          rw [lintegral_union ((measurableSet_boxOf _ _).inter (measurableSet_Dk k))
            (hdisj.mono inter_subset_left inter_subset_left)]
      _ ≤ ∫⁻ x in boxOf lo hi ∩ Dk k, F2 k x :=
          lintegral_mono_set (union_subset
            (inter_subset_inter_left _ (boxOf_lower_subset lo hi d))
            (inter_subset_inter_left _ (boxOf_upper_subset lo hi d)))

/-- A passing external claim bounds the integral over its box. -/
theorem extOK_sound {k : ℕ} {L : List ℤ → List ℤ → ℤ} (hL : LeafSoundProp k L) (x : ExtEntry)
    (h : extOK k L x = true) :
    ENNReal.ofReal ((x.1 : ℝ) / 2 ^ OS) ≤ ∫⁻ y in boxOf x.box.1 x.box.2 ∩ Dk k, F2 k y := by
  simp only [extOK, decide_eq_true_eq] at h
  refine le_trans (ENNReal.ofReal_le_ofReal ?_) (bnbStream_sound hL read4 FUEL x.2.1 x.2.2.1 x.2.2.2)
  exact div_le_div_of_nonneg_right (by exact_mod_cast h) (by positivity)

/-- Soundness of the sub-box shards for one box: a passing `cutOK` and passing claims for all its entries. -/
theorem cutBox_sound {k : ℕ} {L : List ℤ → List ℤ → ℤ} (hL : LeafSoundProp k L) {c : ℕ} {lo hi : List ℤ}
    {X : List ExtEntry} {V : ℤ} (hl : lo.length = mDim k) (hc : cutOK k L c lo hi X V = true)
    (hX : ∀ x ∈ X, extOK k L x = true) :
    ENNReal.ofReal ((V : ℝ) / 2 ^ OS) ≤ ∫⁻ y in boxOf lo hi ∩ Dk k, F2 k y := by
  simp only [cutOK, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨hB, hV⟩ := hc
  refine le_trans (ENNReal.ofReal_le_ofReal ?_) (bnbCut_sound hL read4 FUEL c lo hi (X.map (·.1)) hl ?_)
  · exact div_le_div_of_nonneg_right (by exact_mod_cast hV) (by positivity)
  · intro j hj
    rw [hB] at hj ⊢
    rw [List.length_map] at hj
    have hx := extOK_sound hL (X[j]) (hX _ (List.getElem_mem hj))
    rw [List.getD_eq_getElem _ _ (by simpa using hj), List.getD_eq_getElem _ _ (by simpa using hj)]
    simpa [ExtEntry.box] using hx

/-- passing checks of the chunks give passing claims for every entry of the flattened list -/
theorem extOK_of_chunks {k : ℕ} {L : List ℤ → List ℤ → ℤ} (Xs : List (List ExtEntry))
    (h : ∀ i < Xs.length, subOK k L (Xs.getD i []) = true) : ∀ x ∈ Xs.flatten, extOK k L x = true := by
  intro x hx
  obtain ⟨s, hs, hxs⟩ := List.mem_flatten.1 hx
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hs
  have := h i hi
  rw [List.getD_eq_getElem _ _ hi] at this
  exact List.all_eq_true.1 this x hxs

end BHH.KC

namespace BHH

export KC (bnbCut_rest bnbCut_sound extOK_sound cutBox_sound extOK_of_chunks)

end BHH
