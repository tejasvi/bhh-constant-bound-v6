/-
Module L: invariance under relabeling and translation of the points (`Λ` under graph isomorphisms,
`ĝ ≤ g` after relabeling, the union area).
-/
import W2.LapGamma

open MeasureTheory Set Real
open scoped ENNReal

noncomputable section

namespace BHH.W2

/-! ## `Λ` is invariant under graph isomorphisms -/

lemma nLt2_iso {k : ℕ} {H H' : SimpleGraph (Fin k)} (e : H ≃g H') : nLt2 H = nLt2 H' := by
  classical
  unfold nLt2
  refine Finset.card_bij' (fun v _ => e v) (fun v _ => e.symm v) ?_ ?_ ?_ ?_
  · intro v hv
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
    rw [e.degree_eq]; exact hv
  · intro v hv
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
    rw [e.symm.degree_eq]; exact hv
  · intro v _; simp
  · intro v _; simp

lemma Lam_iso {k : ℕ} {H H' : SimpleGraph (Fin k)} (e : H ≃g H') : Lam H = Lam H' := by
  have hn := nLt2_iso e
  have hc := e.connected_iff
  unfold Lam
  by_cases h : H.Connected
  · have h' : H'.Connected := hc.1 h
    simp only [h, h', ↓reduceIte, hn]
  · have h' : ¬ H'.Connected := fun h' => h (hc.2 h')
    simp only [h, h', ↓reduceIte]

/-- the window graph of a relabeled graph: `Λ ≤ g` -/
lemma Lam_window_comap_le {k : ℕ} (hk : 2 ≤ k) (G : SimpleGraph (Fin k)) (σ : Equiv.Perm (Fin k)) :
    Lam (windowGraph (G.comap σ)) ≤ dcG G := by
  set W := windowGraph (G.comap σ)
  have h1 : W ≤ G.comap σ := windowGraph_le _
  have h2 : W.map σ.toEmbedding ≤ G := SimpleGraph.map_le_iff_le_comap.2 h1
  rw [Lam_iso (SimpleGraph.Iso.map σ W)]
  exact Lam_le_dcG h2 hk

/-! ## Relabeled and translated configurations -/

lemma unitGraph_relabel {k : ℕ} (y : Fin k → Pt) (σ : Equiv.Perm (Fin k)) (c : Pt) :
    unitGraph (fun j => y (σ j) - c) = (unitGraph y).comap σ := by
  ext i j
  simp only [unitGraph, SimpleGraph.comap_adj, ne_eq, EmbeddingLike.apply_eq_iff_eq]
  have : sqDist (y (σ i) - c) (y (σ j) - c) = sqDist (y (σ i)) (y (σ j)) := by
    simp only [sqDist, Prod.fst_sub, Prod.snd_sub]; ring
  rw [this]

lemma unionArea_relabel {k : ℕ} (y : Fin k → Pt) (σ : Equiv.Perm (Fin k)) (c : Pt) :
    unionArea (fun j => y (σ j) - c) = unionArea y := by
  unfold unionArea
  have h1 : (⋃ j, disk (y (σ j) - c) 1) = (fun p => p + c) ⁻¹' ⋃ j, disk (y (σ j)) 1 := by
    ext p
    simp only [mem_iUnion, mem_preimage, disk, sqDist, mem_ofPred_eq, Prod.fst_sub, Prod.snd_sub,
      Prod.fst_add, Prod.snd_add]
    constructor <;> rintro ⟨j, hj⟩ <;> exact ⟨j, by ring_nf; ring_nf at hj; linarith⟩
  have h2 : (⋃ j, disk (y (σ j)) 1) = ⋃ j, disk (y j) 1 := by
    ext p
    simp only [mem_iUnion]
    constructor
    · rintro ⟨j, hj⟩; exact ⟨σ j, hj⟩
    · rintro ⟨j, hj⟩; exact ⟨σ.symm j, by rwa [Equiv.apply_symm_apply]⟩
  rw [h1, measure_preimage_add_right, h2]

end BHH.W2
