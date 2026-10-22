/-
Track K assembly over initial boxes (sub-box shards).

* `RangeBound k R a b V`: `V / 2^OS` bounds the integral of `F2 k` over the initial boxes `t ∈ [a, b)` (of `2^R`)
  intersected with `D_k`.
* Constructors: `rangeBound_of_shardSumK` (a K shard over whole initial boxes, `BHHCert/TreeK.lean`),
  `rangeBound_of_cut` (one initial box from a cut tree and its external claims, `BHHCert/TreeCut.lean`),
  `RangeBound.add` (adjacent ranges), `RangeBound.mono`.
* `C_ge_of_rangeK`: the full range `[0, 2^R)` gives `C_k ≥ (q/2) V / 2^OS` for `0 ≤ q ≤ κ_k` (Lemma 2.2).
* `mainBoundsK1_of`: `MainBoundsK1` from leaf soundness of `LkK 3`, `LkK 4` (module D, `leafSound_K_final`) and
  full-range bounds with the arithmetic checks `c3`, `c4`.
-/
import BHH.TreeCut
import BHH.MainV2
import BHH.StatementK
import BHHCert.ShardK

open MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace BHH.KC

open BHH.Cert BHH.E

/-- the union of the initial boxes `t ∈ [a, b)` of `2^R` -/
def initUnion (k R a b : ℕ) : Set (Fin (mDim k) → ℝ) :=
  ⋃ t ∈ Finset.Ico a b, boxOf (initBox k R t).1 (initBox k R t).2

/-- `V / 2^OS` bounds the integral over the initial boxes `[a, b)` intersected with `D_k` -/
def RangeBound (k R a b : ℕ) (V : ℤ) : Prop :=
  ENNReal.ofReal ((V : ℝ) / 2 ^ OS) ≤ ∫⁻ x in initUnion k R a b ∩ Dk k, F2 k x

lemma measurableSet_initUnion (k R a b : ℕ) : MeasurableSet (initUnion k R a b) :=
  Finset.measurableSet_biUnion _ fun _ _ => measurableSet_boxOf _ _

lemma initUnion_single (k R t : ℕ) :
    initUnion k R t (t + 1) = boxOf (initBox k R t).1 (initBox k R t).2 := by
  ext x
  simp only [initUnion, Finset.mem_Ico, mem_iUnion, exists_prop]
  constructor
  · rintro ⟨t', ⟨h1, h2⟩, hx⟩
    obtain rfl : t' = t := by omega
    exact hx
  · intro hx
    exact ⟨t, ⟨le_rfl, Nat.lt_succ_self t⟩, hx⟩

lemma initUnion_union {k R a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c) :
    initUnion k R a b ∪ initUnion k R b c = initUnion k R a c := by
  ext x
  simp only [initUnion, Finset.mem_Ico, mem_union, mem_iUnion, exists_prop]
  constructor
  · rintro (⟨t, ⟨h1, h2⟩, hx⟩ | ⟨t, ⟨h1, h2⟩, hx⟩)
    · exact ⟨t, ⟨h1, by omega⟩, hx⟩
    · exact ⟨t, ⟨by omega, h2⟩, hx⟩
  · rintro ⟨t, ⟨h1, h2⟩, hx⟩
    by_cases ht : t < b
    · exact Or.inl ⟨t, ⟨h1, ht⟩, hx⟩
    · exact Or.inr ⟨t, ⟨by omega, h2⟩, hx⟩

lemma initUnion_disjoint {k R a b c : ℕ} (hk : 2 ≤ k) (hc : c ≤ 2 ^ R) :
    Disjoint (initUnion k R a b) (initUnion k R b c) := by
  rw [Set.disjoint_left]
  intro x hx hy
  simp only [initUnion, Finset.mem_Ico, mem_iUnion, exists_prop] at hx hy
  obtain ⟨t, ⟨_, h2⟩, hxt⟩ := hx
  obtain ⟨t', ⟨h1', h2'⟩, hxt'⟩ := hy
  exact Set.disjoint_left.1 (initBox_disjoint hk (by omega) (by omega) (by omega)) hxt hxt'

lemma initUnion_subset (k R a b : ℕ) : initUnion k R a b ⊆ Xk k := by
  intro x hx
  simp only [initUnion, Finset.mem_Ico, mem_iUnion, exists_prop] at hx
  obtain ⟨t, _, hxt⟩ := hx
  exact initBox_subset k R t hxt

lemma initBox_length (k R t : ℕ) : (initBox k R t).1.length = mDim k := by
  rw [initBox, (initBoxGo_length t R _ _).1, rootLo_length]

theorem RangeBound.mono {k R a b : ℕ} {V W : ℤ} (h : RangeBound k R a b V) (hW : W ≤ V) :
    RangeBound k R a b W :=
  le_trans (ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right (by exact_mod_cast hW) (by positivity))) h

theorem RangeBound.zero (k R a b : ℕ) : RangeBound k R a b 0 := by
  simp [RangeBound]

theorem RangeBound.empty (k R a : ℕ) : RangeBound k R a a 0 := RangeBound.zero k R a a

/-- adjacent ranges add up -/
theorem RangeBound.add {k R a b c : ℕ} (hk : 2 ≤ k) (hab : a ≤ b) (hbc : b ≤ c) (hc : c ≤ 2 ^ R) {V W : ℤ}
    (h1 : RangeBound k R a b V) (h2 : RangeBound k R b c W) : RangeBound k R a c (V + W) := by
  unfold RangeBound at h1 h2 ⊢
  calc ENNReal.ofReal (((V + W : ℤ) : ℝ) / 2 ^ OS)
      ≤ ENNReal.ofReal ((V : ℝ) / 2 ^ OS) + ENNReal.ofReal ((W : ℝ) / 2 ^ OS) := by
        rw [Int.cast_add, add_div]; exact ENNReal.ofReal_add_le
    _ ≤ (∫⁻ x in initUnion k R a b ∩ Dk k, F2 k x) + ∫⁻ x in initUnion k R b c ∩ Dk k, F2 k x :=
        add_le_add h1 h2
    _ = ∫⁻ x in (initUnion k R a b ∩ Dk k) ∪ (initUnion k R b c ∩ Dk k), F2 k x :=
        (lintegral_union ((measurableSet_initUnion k R b c).inter (measurableSet_Dk k))
          ((initUnion_disjoint hk hc).mono inter_subset_left inter_subset_left)).symm
    _ = ∫⁻ x in initUnion k R a c ∩ Dk k, F2 k x := by
        rw [← Set.union_inter_distrib_right, initUnion_union hab hbc]

/-- one initial box from its K tree (`bnbStream` with the code `c`) -/
theorem rangeBound_of_treeK {k : ℕ} {L : List ℤ → List ℤ → ℤ} (hL : LeafSoundProp k L) (R t c : ℕ) :
    RangeBound k R t (t + 1) (treeK k L R t c) := by
  rw [RangeBound, initUnion_single]
  exact bnbStream_sound hL read4 _ _ _ _

/-- a K shard over the whole initial boxes `a, …, a + |codes| - 1` -/
theorem rangeBound_of_shardSumK {k : ℕ} (hk : 2 ≤ k) {L : List ℤ → List ℤ → ℤ} (hL : LeafSoundProp k L)
    {R : ℕ} : ∀ (codes : List ℕ) (a : ℕ), a + codes.length ≤ 2 ^ R →
      RangeBound k R a (a + codes.length) (shardSumK k L R a codes)
  | [], a, _ => by simpa [shardSumK] using RangeBound.empty k R a
  | c :: cs, a, hb => by
    rw [shardSumK, List.length_cons, show a + (cs.length + 1) = a + 1 + cs.length by omega]
    exact RangeBound.add hk (Nat.le_succ a) (by omega) (by simp at hb; omega) (rangeBound_of_treeK hL R a c)
      (rangeBound_of_shardSumK hk hL cs (a + 1) (by simp at hb; omega))

/-- a lower bound of a K shard over whole initial boxes -/
theorem rangeBound_of_le_shardSumK {k : ℕ} (hk : 2 ≤ k) {L : List ℤ → List ℤ → ℤ} (hL : LeafSoundProp k L)
    {R a : ℕ} (codes : List ℕ) (hb : a + codes.length ≤ 2 ^ R) {V : ℤ} (hV : V ≤ shardSumK k L R a codes) :
    RangeBound k R a (a + codes.length) V :=
  (rangeBound_of_shardSumK hk hL codes a hb).mono hV

/-- one initial box from a cut tree (`cutOK`) and passing claims for all its external entries -/
theorem rangeBound_of_cut {k : ℕ} {L : List ℤ → List ℤ → ℤ} (hL : LeafSoundProp k L) {R t c : ℕ}
    {X : List ExtEntry} {V : ℤ} (hc : cutOK k L c (initBox k R t).1 (initBox k R t).2 X V = true)
    (hX : ∀ x ∈ X, extOK k L x = true) : RangeBound k R t (t + 1) V := by
  rw [RangeBound, initUnion_single]
  exact cutBox_sound hL (initBox_length k R t) hc hX

/-- one term `C_k` from a bound over all initial boxes -/
theorem C_ge_of_rangeK {k : ℕ} (hk : 3 ≤ k) {R : ℕ} {S : ℤ} (hS : RangeBound k R 0 (2 ^ R) S) {q t : ℝ}
    (hq0 : 0 ≤ q) (hq : q ≤ kappa k) (ht : t ≤ q / 2 * ((S : ℝ) / 2 ^ OS)) : ENNReal.ofReal t ≤ C k := by
  have hdom := domainReductionProp_of_three_le hk
  have hsh : ENNReal.ofReal ((S : ℝ) / 2 ^ OS) ≤ ∫⁻ x in Dk k ∩ Xk k, F2 k x :=
    le_trans hS (lintegral_mono_set (fun x hx => ⟨hx.2, initUnion_subset k R 0 (2 ^ R) hx.1⟩))
  by_cases hS0 : S < 0
  · have h0 : q / 2 * ((S : ℝ) / 2 ^ OS) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity)
        (div_nonpos_of_nonpos_of_nonneg (by exact_mod_cast hS0.le) (by positivity))
    rw [ENNReal.ofReal_of_nonpos (ht.trans h0)]
    exact zero_le
  push Not at hS0
  have hκ : 0 ≤ kappa k / 2 := by linarith
  have hSr : (0 : ℝ) ≤ (S : ℝ) / 2 ^ OS := div_nonneg (by exact_mod_cast hS0) (by positivity)
  calc ENNReal.ofReal t ≤ ENNReal.ofReal (kappa k / 2 * ((S : ℝ) / 2 ^ OS)) :=
        ENNReal.ofReal_le_ofReal (ht.trans (mul_le_mul_of_nonneg_right (by linarith) hSr))
    _ = ENNReal.ofReal (kappa k / 2) * ENNReal.ofReal ((S : ℝ) / 2 ^ OS) := ENNReal.ofReal_mul hκ
    _ ≤ ENNReal.ofReal (kappa k / 2) * ∫⁻ x in Dk k ∩ Xk k, F2 k x := mul_le_mul_right hsh _
    _ ≤ C k := hdom

/-- `MainBoundsK1` from leaf soundness of the track-K leaf functions and bounds over all initial boxes -/
theorem mainBoundsK1_of
    (hL : GreenFormula → VertexLemmaSeg → ∀ k : ℕ, 3 ≤ k → k ≤ 4 → LeafSoundProp k (LkK k))
    {S3 S4 : ℤ} (h3 : LeafSoundProp 3 (LkK 3) → RangeBound 3 RNK 0 (2 ^ RNK) S3)
    (h4 : LeafSoundProp 4 (LkK 4) → RangeBound 4 RNK 0 (2 ^ RNK) S4)
    (c3 : (117028397 / 10 ^ 10 : ℝ) ≤ 1 / 4 * piThreeHalvesLo / 2 * ((S3 : ℝ) / 2 ^ OS))
    (c4 : (54272702 / 10 ^ 10 : ℝ) ≤ 5 / 16 * piThreeHalvesLo / 2 * ((S4 : ℝ) / 2 ^ OS)) :
    MainBoundsK1 := by
  intro hG hV
  have hp := piThreeHalvesLo_nonneg
  refine ⟨?_, ?_⟩
  · exact C_ge_of_rangeK (by norm_num) (h3 (hL hG hV 3 le_rfl (by norm_num))) (by positivity)
      kappa_three_gt.le c3
  · exact C_ge_of_rangeK (by norm_num) (h4 (hL hG hV 4 (by norm_num) le_rfl)) (by positivity)
      kappa_four_gt.le c4

end BHH.KC

namespace BHH

export KC (initUnion RangeBound RangeBound.mono RangeBound.zero RangeBound.empty RangeBound.add rangeBound_of_treeK
  rangeBound_of_shardSumK rangeBound_of_le_shardSumK rangeBound_of_cut C_ge_of_rangeK mainBoundsK1_of)

end BHH
