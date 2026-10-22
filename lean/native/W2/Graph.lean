/-
The value `Λ` of the window graph and Lemma 4.2 of the paper (`0 ≤ ĝ ≤ g`).

For a graph `H` on `Fin k`, `nLt2 H` is the number of vertices of degree `< 2`, and
`Lam H = max(0, 1 - nLt2 H / 2)` if `H` is connected, `0` otherwise.  `Lam` is monotone under adding edges, and for
every spanning subgraph `H ≤ G` (`k ≥ 2`) we have `0 ≤ Lam H ≤ dcG G` (Dong-Cao's `g`).
-/
import BHH.Defs

open SimpleGraph

namespace BHH.W2

variable {k : ℕ}

/-- The window graph: the edges of `G` between vertices at most two apart. -/
def windowGraph (G : SimpleGraph (Fin k)) : SimpleGraph (Fin k) where
  Adj a b := G.Adj a b ∧ a.val ≤ b.val + 2 ∧ b.val ≤ a.val + 2
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun a h => G.loopless.irrefl a h.1⟩

lemma windowGraph_le (G : SimpleGraph (Fin k)) : windowGraph G ≤ G := fun _ _ h => h.1

/-- The number of vertices of degree `< 2`. -/
noncomputable def nLt2 (H : SimpleGraph (Fin k)) : ℕ := by
  classical exact (Finset.univ.filter fun v => H.degree v < 2).card

/-- `Λ(H)` (paper Section 4.2). -/
noncomputable def Lam (H : SimpleGraph (Fin k)) : ℝ := by
  classical exact if H.Connected then max 0 (1 - (nLt2 H : ℝ) / 2) else 0

lemma Lam_nonneg (H : SimpleGraph (Fin k)) : 0 ≤ Lam H := by
  unfold Lam; split_ifs <;> simp

/-- Adding edges does not increase `nLt2`. -/
lemma nLt2_anti {H H' : SimpleGraph (Fin k)} (h : H ≤ H') : nLt2 H' ≤ nLt2 H := by
  classical
  unfold nLt2
  apply Finset.card_le_card
  intro v hv
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
  exact lt_of_le_of_lt (degree_le_of_le h) hv

/-- `Λ` is monotone under adding edges. -/
lemma Lam_mono {H H' : SimpleGraph (Fin k)} (h : H ≤ H') : Lam H ≤ Lam H' := by
  classical
  unfold Lam
  by_cases hc : H.Connected
  · have hc' : H'.Connected := hc.mono h
    simp only [hc, hc', ite_true]
    have := nLt2_anti h
    have : (nLt2 H' : ℝ) ≤ nLt2 H := by exact_mod_cast this
    apply max_le_max le_rfl
    linarith
  · simp only [hc, ite_false]
    split_ifs <;> simp

/-- In a connected graph on `≥ 2` vertices every vertex has degree `≥ 1`, so `D(G) = n_1(G)/2`. -/
lemma dcD_eq_of_connected (G : SimpleGraph (Fin k)) (hk : 2 ≤ k) (hG : G.Connected) :
    dcD G = (n1 G : ℝ) / 2 := by
  classical
  have : Nontrivial (Fin k) := Fin.nontrivial_iff_two_le.mpr hk
  unfold dcD n1
  rw [Finset.card_filter, Nat.cast_sum]
  have hsum : ∑ v, max (2 - (G.degree v : ℝ)) 0 = ∑ v, ((if G.degree v = 1 then 1 else 0 : ℕ) : ℝ) := by
    refine Finset.sum_congr rfl fun v _ => ?_
    have hpos : 0 < G.degree v := hG.preconnected.degree_pos_of_nontrivial v
    rcases Nat.lt_or_ge (G.degree v) 2 with h2 | h2
    · have h1 : G.degree v = 1 := by omega
      simp only [h1, ite_true, Nat.cast_one]
      norm_num
    · have hne : G.degree v ≠ 1 := by omega
      simp only [hne, ite_false, Nat.cast_zero]
      have : (2 : ℝ) ≤ G.degree v := by exact_mod_cast h2
      exact max_eq_right (by linarith)
  rw [hsum]
  ring

lemma dcQ_ge_one (G : SimpleGraph (Fin k)) : (1 : ℤ) ≤ dcQ G := by
  unfold dcQ
  exact le_trans (le_max_left _ _) (le_max_left _ _)

lemma dcQ_ge_n1 (G : SimpleGraph (Fin k)) : (n1 G : ℝ) / 2 ≤ (dcQ G : ℝ) := by
  have h1 : ⌈(n1 G : ℝ) / 2⌉ ≤ dcQ G := by
    unfold dcQ
    exact le_trans (le_max_right _ _) (le_max_left _ _)
  have h2 : (n1 G : ℝ) / 2 ≤ (⌈(n1 G : ℝ) / 2⌉ : ℝ) := Int.le_ceil _
  have h3 : ((⌈(n1 G : ℝ) / 2⌉ : ℤ) : ℝ) ≤ (dcQ G : ℝ) := by exact_mod_cast h1
  linarith

/-- Dong-Cao's `g` is nonnegative (`k ≥ 2`). -/
lemma dcG_nonneg (G : SimpleGraph (Fin k)) (hk : 2 ≤ k) : 0 ≤ dcG G := by
  classical
  unfold dcG
  split_ifs with hG
  · rw [dcD_eq_of_connected G hk hG]
    linarith [dcQ_ge_n1 G]
  · exact le_rfl

/-- `n_1(G) ≤ nLt2(H)` for `H ≤ G`. -/
lemma n1_le_nLt2 {H G : SimpleGraph (Fin k)} (h : H ≤ G) : n1 G ≤ nLt2 H := by
  classical
  unfold n1 nLt2
  apply Finset.card_le_card
  intro v hv
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
  have := degree_le_of_le (v := v) h
  omega

/-- Lemma 4.2: `0 ≤ Λ(H) ≤ g(G)` for every spanning subgraph `H ≤ G`, `k ≥ 2`. -/
theorem Lam_le_dcG {H G : SimpleGraph (Fin k)} (h : H ≤ G) (hk : 2 ≤ k) : Lam H ≤ dcG G := by
  classical
  unfold Lam
  split_ifs with hH
  · have hG : G.Connected := hH.mono h
    have e : dcG G = (dcQ G : ℝ) - (n1 G : ℝ) / 2 := by
      unfold dcG; simp only [hG, ite_true]; rw [dcD_eq_of_connected G hk hG]
    rw [e]
    have h1 : (1 : ℝ) ≤ dcQ G := by exact_mod_cast dcQ_ge_one G
    have h2 : (n1 G : ℝ) ≤ nLt2 H := by exact_mod_cast n1_le_nLt2 h
    have h3 := dcQ_ge_n1 G
    apply max_le <;> linarith
  · exact dcG_nonneg G hk

end BHH.W2
