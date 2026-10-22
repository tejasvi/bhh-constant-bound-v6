/-
Module L: the window-2 area bound `A(y(z)) ≤ π + A_1(z_0) + Σ_{j ≥ 1} A_2(z_{j-1}, z_j)` and
`A ≥ π` (paper Lemma 4.4, first part).
-/
import W2.DiscCells

open MeasureTheory Set Real
open scoped ENNReal

noncomputable section

namespace BHH.W2

variable {m : ℕ}

/-- the points `y_i = Σ_{j < i} z_j` indexed by `ℕ` -/
def yN (z : Fin m → Pt) (i : ℕ) : Pt := ∑ j ∈ Finset.range i, zget z j

lemma yN_zero (z : Fin m → Pt) : yN z 0 = 0 := by simp [yN]

lemma yN_succ (z : Fin m → Pt) (i : ℕ) : yN z (i + 1) = yN z i + zget z i := by
  simp [yN, Finset.sum_range_succ]

lemma psum_eq_yN (z : Fin m → Pt) (i : Fin (m + 1)) : psum z i = yN z i.val := by
  have hi : i.val ≤ m := Nat.lt_succ_iff.1 i.isLt
  unfold psum yN
  have e : ∀ j : Fin m, (if j.val < i.val then z j else 0) =
      (fun l => if l < i.val then zget z l else 0) j.val := by
    intro j; simp [zget, j.isLt]
  rw [Finset.sum_congr rfl (fun j _ => e j), Fin.sum_univ_eq_sum_range (fun l => if l < i.val then zget z l else 0) m,
    ← Finset.sum_filter]
  congr 1
  ext l; simp only [Finset.mem_filter, Finset.mem_range]; omega

/-- translation invariance of the areas of differences of disks -/
lemma volume_disk_diff_translate (a b c v : Pt) :
    volume (disk (a + v) 1 \ (disk (b + v) 1 ∪ disk (c + v) 1)) = volume (disk a 1 \ (disk b 1 ∪ disk c 1)) := by
  have e : disk (a + v) 1 \ (disk (b + v) 1 ∪ disk (c + v) 1) =
      (fun p => p + (-v)) ⁻¹' (disk a 1 \ (disk b 1 ∪ disk c 1)) := by
    ext p
    simp only [disk, sqDist, mem_sdiff, mem_union, mem_ofPred_eq, mem_preimage, Prod.fst_add, Prod.snd_add,
      Prod.fst_neg, Prod.snd_neg]
    ring_nf
  rw [e, measure_preimage_add_right]

lemma disk_union_finite (y : ℕ → Pt) (n : ℕ) :
    volume (⋃ i ∈ Finset.range n, disk (y i) 1) ≠ ⊤ := by
  refine ne_top_of_le_ne_top ?_ (measure_biUnion_finset_le _ _)
  exact ENNReal.sum_ne_top.2 fun i _ => by rw [volume_disk_one]; exact ENNReal.ofReal_ne_top

/-- the prefix bound by induction on the number of disks -/
lemma volume_prefix_le (z : Fin m → Pt) : ∀ n : ℕ,
    volume (⋃ i ∈ Finset.range (n + 2), disk (yN z i) 1) ≤
      ENNReal.ofReal (π + A1 (zget z 0) + ∑ j ∈ Finset.Ico 1 (n + 1), A2 (zget z (j - 1)) (zget z j))
  | 0 => by
    have e : (⋃ i ∈ Finset.range 2, disk (yN z i) 1) ⊆ disk 0 1 ∪ (disk (zget z 0) 1 \ disk 0 1) := by
      intro p hp
      simp only [Finset.mem_range, mem_iUnion] at hp
      obtain ⟨i, hi, hp⟩ := hp
      interval_cases i
      · simp only [yN_zero] at hp; exact Or.inl hp
      · rw [yN_succ, yN_zero, zero_add] at hp
        by_cases h0 : p ∈ disk 0 1
        · exact Or.inl h0
        · exact Or.inr ⟨hp, h0⟩
    calc volume (⋃ i ∈ Finset.range 2, disk (yN z i) 1)
        ≤ volume (disk 0 1) + volume (disk (zget z 0) 1 \ disk 0 1) := (measure_mono e).trans (measure_union_le _ _)
      _ = ENNReal.ofReal π + ENNReal.ofReal (A1 (zget z 0)) := by
          rw [volume_disk_one, A1, ENNReal.ofReal_toReal]
          exact ne_top_of_le_ne_top (by rw [volume_disk_one]; exact ENNReal.ofReal_ne_top) (measure_mono sdiff_subset)
      _ = ENNReal.ofReal (π + A1 (zget z 0) + ∑ j ∈ Finset.Ico 1 (0 + 1), A2 (zget z (j - 1)) (zget z j)) := by
          simp only [zero_add, Finset.Ico_self, Finset.sum_empty, add_zero]
          rw [ENNReal.ofReal_add Real.pi_pos.le (A1_nonneg _)]
  | n + 1 => by
    have ih := volume_prefix_le z n
    have e : (⋃ i ∈ Finset.range (n + 1 + 2), disk (yN z i) 1) ⊆ (⋃ i ∈ Finset.range (n + 2), disk (yN z i) 1) ∪
        (disk (yN z (n + 2)) 1 \ (disk (yN z (n + 1)) 1 ∪ disk (yN z n) 1)) := by
      intro p hp
      simp only [Finset.mem_range, mem_iUnion] at hp
      obtain ⟨i, hi, hp⟩ := hp
      by_cases hin : i < n + 2
      · exact Or.inl (mem_biUnion (Finset.mem_range.2 hin) hp)
      · have hi2 : i = n + 2 := by omega
        subst hi2
        by_cases h1 : p ∈ disk (yN z (n + 1)) 1 ∪ disk (yN z n) 1
        · rcases h1 with h1 | h1
          · exact Or.inl (mem_biUnion (Finset.mem_range.2 (by omega)) h1)
          · exact Or.inl (mem_biUnion (Finset.mem_range.2 (by omega)) h1)
        · exact Or.inr ⟨hp, h1⟩
    have hA2 : volume (disk (yN z (n + 2)) 1 \ (disk (yN z (n + 1)) 1 ∪ disk (yN z n) 1)) =
        ENNReal.ofReal (A2 (zget z n) (zget z (n + 1))) := by
      have h1 : yN z (n + 2) = zget z (n + 1) + yN z (n + 1) := by rw [yN_succ, add_comm]
      have h3 : yN z n = -zget z n + yN z (n + 1) := by rw [yN_succ]; abel
      have ht := volume_disk_diff_translate (zget z (n + 1)) 0 (-zget z n) (yN z (n + 1))
      rw [zero_add] at ht
      rw [h1, h3, ht, A2, ENNReal.ofReal_toReal]
      exact ne_top_of_le_ne_top (by rw [volume_disk_one]; exact ENNReal.ofReal_ne_top) (measure_mono sdiff_subset)
    calc volume (⋃ i ∈ Finset.range (n + 1 + 2), disk (yN z i) 1)
        ≤ volume (⋃ i ∈ Finset.range (n + 2), disk (yN z i) 1) +
            volume (disk (yN z (n + 2)) 1 \ (disk (yN z (n + 1)) 1 ∪ disk (yN z n) 1)) :=
          (measure_mono e).trans (measure_union_le _ _)
      _ ≤ ENNReal.ofReal (π + A1 (zget z 0) + ∑ j ∈ Finset.Ico 1 (n + 1), A2 (zget z (j - 1)) (zget z j)) +
            ENNReal.ofReal (A2 (zget z n) (zget z (n + 1))) := by rw [hA2]; exact add_le_add ih le_rfl
      _ = ENNReal.ofReal (π + A1 (zget z 0) + ∑ j ∈ Finset.Ico 1 (n + 1 + 1), A2 (zget z (j - 1)) (zget z j)) := by
          rw [← ENNReal.ofReal_add (by
              have := A1_nonneg (zget z 0)
              have : 0 ≤ ∑ j ∈ Finset.Ico 1 (n + 1), A2 (zget z (j - 1)) (zget z j) :=
                Finset.sum_nonneg fun _ _ => A2_nonneg _ _
              linarith [Real.pi_pos]) (A2_nonneg _ _)]
          congr 1
          rw [Finset.sum_Ico_succ_top (by omega : 1 ≤ n + 1), Nat.add_sub_cancel]
          ring

/-- the window-2 area bound -/
theorem unionArea_psum_le (z : Fin m → Pt) : unionArea (psum z) ≤ π + Xsum z := by
  have hU : (⋃ i, disk (psum z i) 1) = ⋃ i ∈ Finset.range (m + 1), disk (yN z i) 1 := by
    ext p
    simp only [mem_iUnion, Finset.mem_range]
    constructor
    · rintro ⟨i, hi⟩; exact ⟨i.val, i.isLt, by rwa [← psum_eq_yN]⟩
    · rintro ⟨i, hi, hp⟩; exact ⟨⟨i, hi⟩, by rwa [psum_eq_yN]⟩
  unfold unionArea Xsum
  rw [hU]
  rcases Nat.lt_or_ge m 1 with hm | hm
  · -- no increments: one disk
    have hm0 : m = 0 := by omega
    subst hm0
    simp only [zero_add, Finset.range_one, Finset.mem_singleton, iUnion_iUnion_eq_left, yN_zero,
      Finset.Ico_eq_empty_of_le (show 0 ≤ 1 by omega), Finset.sum_empty, add_zero]
    rw [volume_disk_one, ENNReal.toReal_ofReal Real.pi_pos.le]
    linarith [A1_nonneg (zget z 0)]
  · obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
    have h := volume_prefix_le z n
    have hnn : 0 ≤ π + A1 (zget z 0) + ∑ j ∈ Finset.Ico 1 (n + 1), A2 (zget z (j - 1)) (zget z j) := by
      have := A1_nonneg (zget z 0)
      have : 0 ≤ ∑ j ∈ Finset.Ico 1 (n + 1), A2 (zget z (j - 1)) (zget z j) :=
        Finset.sum_nonneg fun _ _ => A2_nonneg _ _
      linarith [Real.pi_pos]
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
    rw [ENNReal.toReal_ofReal hnn] at this
    linarith

/-- `A(y) ≥ π` -/
theorem pi_le_unionArea_psum (z : Fin m → Pt) : π ≤ unionArea (psum z) := by
  unfold unionArea
  have hfin : volume (⋃ i, disk (psum z i) 1) ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (measure_iUnion_fintype_le volume _)
    exact ENNReal.sum_ne_top.2 fun i _ => by rw [volume_disk_one]; exact ENNReal.ofReal_ne_top
  have h := ENNReal.toReal_mono hfin (measure_mono (Set.subset_iUnion (fun i => disk (psum z i) 1) 0))
  rwa [volume_disk_one, ENNReal.toReal_ofReal Real.pi_pos.le] at h

end BHH.W2
