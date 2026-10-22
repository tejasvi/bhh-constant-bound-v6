/-
Soundness of the data-driven bisection tree of track K (`BHHCert/TreeK.lean`), for every stream of node codes:
`bnbStream_sound` (one box) and `shardSumK_sound` (a shard of initial boxes with one code each), as `bnbExact_sound` and
`shardSum_sound` in BHH/Tree.lean.
-/
import BHH.Tree
import BHHCert.TreeK

open MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace BHH.E

open BHH.Cert

lemma bnbStream_nonneg {S : Type} (k : ℕ) (L : List ℤ → List ℤ → ℤ) (read : S → ℕ × S) :
    ∀ fuel (s : S) lo hi, 0 ≤ (bnbStream k L read fuel s lo hi).1 := by
  intro fuel
  induction fuel with
  | zero => intro s lo hi; simp [bnbStream]
  | succ n ih =>
    intro s lo hi
    simp only [bnbStream]
    split_ifs
    · exact le_max_right _ _
    · exact le_refl 0
    · exact add_nonneg (ih _ _ _) (ih _ _ _)
    · exact le_refl 0
    · exact le_refl 0

lemma bnbStream_length {S : Type} (k : ℕ) (L : List ℤ → List ℤ → ℤ) (read : S → ℕ × S) :
    ∀ fuel (s : S) lo hi, lo.length ≠ mDim k → (bnbStream k L read fuel s lo hi).1 = 0 := by
  intro fuel
  induction fuel with
  | zero => intro s lo hi _; simp [bnbStream]
  | succ n ih =>
    intro s lo hi hl
    simp only [bnbStream]
    split_ifs with h1 hv h2 hd
    · exact absurd (validB_valid hv).1 hl
    · rfl
    · simp only
      rw [ih _ _ _ hl, ih _ _ _ (by simpa using hl)]
      rfl
    · rfl
    · rfl

/-- Soundness of the data-driven recursion, for every stream of node codes. -/
theorem bnbStream_sound {S : Type} {k : ℕ} {L : List ℤ → List ℤ → ℤ} (hL : LeafSoundProp k L)
    (read : S → ℕ × S) (fuel : ℕ) (s : S) (lo hi : List ℤ) :
    ENNReal.ofReal (((bnbStream k L read fuel s lo hi).1 : ℝ) / 2 ^ OS) ≤
      ∫⁻ x in boxOf lo hi ∩ Dk k, F2 k x := by
  by_cases hl : lo.length = mDim k
  swap
  · rw [bnbStream_length k L read fuel s lo hi hl]; simp
  induction fuel generalizing s lo hi with
  | zero => simp [bnbStream]
  | succ n ih =>
    simp only [bnbStream]
    split_ifs with h1 hv h2 hd
    · exact ofReal_max_div_le (by positivity) (hL lo hi (validB_valid hv))
    · simp
    · simp only
      set d := (read s).1 - 2
      set mid := (lo.getD d 0 + hi.getD d 0) / 2
      set r1 := bnbStream k L read n (read s).2 lo (hi.set d mid)
      set r2 := bnbStream k L read n r1.2 (lo.set d mid) hi
      have hA := ih (read s).2 lo (hi.set d mid) hl
      have hB := ih r1.2 (lo.set d mid) hi (by simpa using hl)
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
    · simp
    · simp

lemma treeK_nonneg (k : ℕ) (L : List ℤ → List ℤ → ℤ) (R t c : ℕ) : 0 ≤ treeK k L R t c :=
  bnbStream_nonneg k L read4 _ _ _ _

lemma shardSumK_eq_sum (k : ℕ) (L : List ℤ → List ℤ → ℤ) (R : ℕ) :
    ∀ (codes : List ℕ) (a : ℕ),
      shardSumK k L R a codes = ∑ i ∈ Finset.range codes.length, treeK k L R (a + i) (codes.getD i 0)
  | [], a => by simp [shardSumK]
  | c :: cs, a => by
    rw [shardSumK, shardSumK_eq_sum k L R cs (a + 1), List.length_cons, Finset.sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero, add_zero]
    rw [add_comm]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    omega

/-- Soundness of a K shard, for every list of tree codes. -/
theorem shardSumK_sound {k : ℕ} (hk : 2 ≤ k) {L : List ℤ → List ℤ → ℤ} (hL : LeafSoundProp k L)
    {R a : ℕ} (codes : List ℕ) (hb : a + codes.length ≤ 2 ^ R) :
    ENNReal.ofReal ((shardSumK k L R a codes : ℝ) / 2 ^ OS) ≤ ∫⁻ x in Dk k ∩ Xk k, F2 k x := by
  set B : ℕ → Set (Fin (mDim k) → ℝ) := fun i => boxOf (initBox k R (a + i)).1 (initBox k R (a + i)).2
  have hdisj : Set.PairwiseDisjoint (↑(Finset.range codes.length)) fun i => B i ∩ Dk k := by
    intro i hi j hj hij
    simp only [Finset.coe_range, mem_Iio] at hi hj
    exact (initBox_disjoint hk (by omega) (by omega) (by omega)).mono inter_subset_left inter_subset_left
  calc ENNReal.ofReal ((shardSumK k L R a codes : ℝ) / 2 ^ OS)
      = ∑ i ∈ Finset.range codes.length,
          ENNReal.ofReal ((treeK k L R (a + i) (codes.getD i 0) : ℝ) / 2 ^ OS) := by
        rw [shardSumK_eq_sum, Int.cast_sum, Finset.sum_div]
        exact ENNReal.ofReal_sum_of_nonneg fun i _ =>
          div_nonneg (by exact_mod_cast treeK_nonneg k L R _ _) (by positivity)
    _ ≤ ∑ i ∈ Finset.range codes.length, ∫⁻ x in B i ∩ Dk k, F2 k x :=
        Finset.sum_le_sum fun i _ => bnbStream_sound hL read4 _ _ _ _
    _ = ∫⁻ x in ⋃ i ∈ Finset.range codes.length, B i ∩ Dk k, F2 k x :=
        (lintegral_biUnion_finset hdisj (fun i _ => (measurableSet_boxOf _ _).inter (measurableSet_Dk k)) _).symm
    _ ≤ ∫⁻ x in Dk k ∩ Xk k, F2 k x := by
        apply lintegral_mono_set
        intro x hx
        simp only [mem_iUnion, mem_inter_iff] at hx
        obtain ⟨i, _, hxB, hxD⟩ := hx
        exact ⟨hxD, initBox_subset k R (a + i) hxB⟩

end BHH.E

namespace BHH

-- the deliverables of this file, also under `BHH` (helpers stay in `BHH.E`)
export E (bnbStream_nonneg bnbStream_sound treeK_nonneg shardSumK_eq_sum shardSumK_sound)

end BHH
