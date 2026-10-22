/-
`CFinite` (module E, item 5): every `C_k` is finite.

`g(G) ≤ |V|`; if `g(G_1(y)) ≠ 0` then `G_1(y)` is connected, so every point is joined to `y_1 = 0` by a path of at most
`k - 1` edges of length at most `1`, and the configuration lies in the box `[-(k-1), k-1]^{2(k-1)}`; the union area is
at least `1` (it contains the unit square around `0`).  Hence the integrand is at most `k` times the indicator of a
box of finite volume.
-/
import BHH.Graph
import BHH.StatementV2

open MeasureTheory Set Real
open scoped ENNReal

noncomputable section

namespace BHH.E

/-! ## `g ≤ |V|` -/

lemma ccDel_le_card {V : Type*} [Fintype V] (G : SimpleGraph V) (S : Finset V) :
    ccDel G S ≤ Fintype.card V := by
  classical
  unfold ccDel
  set H := G.induce ((S : Set V)ᶜ)
  rw [Nat.card_eq_fintype_card]
  calc Fintype.card H.ConnectedComponent ≤ Fintype.card ((S : Set V)ᶜ : Set V) :=
        Fintype.card_le_of_surjective H.connectedComponentMk fun c => Quot.exists_rep c
    _ ≤ Fintype.card V := Fintype.card_subtype_le _

lemma dcQ_le_card {V : Type*} [Fintype V] [Nonempty V] (G : SimpleGraph V) : dcQ G ≤ Fintype.card V := by
  classical
  unfold dcQ
  refine max_le (max_le ?_ ?_) (Finset.sup'_le _ _ fun S _ => ?_)
  · exact_mod_cast Fintype.card_pos
  · rw [Int.ceil_le]
    have h1 : n1 G ≤ Fintype.card V := by
      unfold n1
      exact (Finset.card_filter_le _ _).trans (by rw [Finset.card_univ])
    have h2 : (n1 G : ℝ) ≤ Fintype.card V := by exact_mod_cast h1
    push_cast
    linarith
  · have := ccDel_le_card G S
    omega

lemma dcD_nonneg {V : Type*} [Fintype V] (G : SimpleGraph V) : 0 ≤ dcD G := by
  unfold dcD
  exact mul_nonneg (by norm_num) (Finset.sum_nonneg fun v _ => le_max_right _ _)

lemma dcG_le_card {V : Type*} [Fintype V] (G : SimpleGraph V) : dcG G ≤ Fintype.card V := by
  unfold dcG
  split_ifs with hc
  · have : Nonempty V := hc.nonempty
    have h1 : (dcQ G : ℝ) ≤ Fintype.card V := by exact_mod_cast dcQ_le_card G
    linarith [dcD_nonneg G]
  · positivity

/-! ## connected configurations lie in a box -/

lemma abs_sub_le_of_sqDist {a b : Pt} (h : sqDist a b ≤ 1) : |a.1 - b.1| ≤ 1 ∧ |a.2 - b.2| ≤ 1 := by
  unfold sqDist at h
  constructor
  · rw [abs_le]; constructor <;> nlinarith [sq_nonneg (a.2 - b.2)]
  · rw [abs_le]; constructor <;> nlinarith [sq_nonneg (a.1 - b.1)]

lemma walk_coord_bound {k : ℕ} (y : Fin k → Pt) {u v : Fin k} (p : (unitGraph y).Walk u v) :
    |(y v).1 - (y u).1| ≤ p.length ∧ |(y v).2 - (y u).2| ≤ p.length := by
  induction p with
  | nil => simp
  | @cons a b c h p ih =>
    have hab := abs_sub_le_of_sqDist h.2
    simp only [SimpleGraph.Walk.length_cons]
    push_cast
    constructor
    · calc |(y c).1 - (y a).1| ≤ |(y c).1 - (y b).1| + |(y b).1 - (y a).1| := abs_sub_le _ _ _
        _ ≤ p.length + 1 := add_le_add ih.1 (by rw [abs_sub_comm]; exact hab.1)
    · calc |(y c).2 - (y a).2| ≤ |(y c).2 - (y b).2| + |(y b).2 - (y a).2| := abs_sub_le _ _ _
        _ ≤ p.length + 1 := add_le_add ih.2 (by rw [abs_sub_comm]; exact hab.2)

/-- the box `[-m, m]^{2m}` -/
def boxM (m : ℕ) : Set (Fin m → Pt) := Set.pi univ fun _ => Icc (-(m : ℝ)) m ×ˢ Icc (-(m : ℝ)) m

lemma cfg_mem_boxM {m : ℕ} (z : Fin m → Pt) (hc : (unitGraph (cfg z)).Connected) : z ∈ boxM m := by
  classical
  intro i _
  obtain ⟨p⟩ := hc.preconnected 0 i.succ
  have hlen := p.toPath.property.length_lt
  have hb := walk_coord_bound (cfg z) (p.toPath : (unitGraph (cfg z)).Walk 0 i.succ)
  simp only [cfg, Fin.cons_zero, Fin.cons_succ, Fintype.card_fin] at hb hlen
  have hl : ((p.toPath : (unitGraph (cfg z)).Walk 0 i.succ).length : ℝ) ≤ m := by
    exact_mod_cast Nat.lt_succ_iff.mp hlen
  simp only [Prod.fst_zero, Prod.snd_zero, sub_zero] at hb
  simp only [mem_prod, mem_Icc]
  rw [← abs_le, ← abs_le]
  exact ⟨hb.1.trans hl, hb.2.trans hl⟩

/-! ## the union area is at least `1` -/

lemma one_le_unionArea_cfg {m : ℕ} (z : Fin m → Pt) : 1 ≤ unionArea (cfg z) := by
  unfold unionArea
  set U := ⋃ i, disk (cfg z i) 1 with hU
  have hsq : (Icc (-(1 / 2 : ℝ)) (1 / 2) ×ˢ Icc (-(1 / 2 : ℝ)) (1 / 2)) ⊆ U := by
    intro p hp
    refine mem_iUnion.mpr ⟨0, ?_⟩
    simp only [mem_prod, mem_Icc] at hp
    simp only [cfg, Fin.cons_zero, disk, mem_ofPred_eq, sqDist, Prod.fst_zero, Prod.snd_zero, sub_zero]
    nlinarith [hp.1.1, hp.1.2, hp.2.1, hp.2.2]
  have h1 : (1 : ℝ≥0∞) ≤ volume U := by
    calc (1 : ℝ≥0∞) = volume (Icc (-(1 / 2 : ℝ)) (1 / 2) ×ˢ Icc (-(1 / 2 : ℝ)) (1 / 2)) := by
          rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Icc]
          norm_num
      _ ≤ volume U := measure_mono hsq
  have hbd : Bornology.IsBounded U := by
    rw [hU, Bornology.isBounded_iUnion]
    intro i
    refine (Metric.isBounded_closedBall (x := cfg z i) (r := 1)).subset fun p hp => ?_
    have h := abs_sub_le_of_sqDist (by simpa [disk] using hp)
    rw [Metric.mem_closedBall, Prod.dist_eq, Real.dist_eq, Real.dist_eq]
    exact max_le h.1 h.2
  have := ENNReal.toReal_mono hbd.measure_lt_top.ne h1
  simpa using this

/-! ## `C_k < ∞` -/

lemma ckIntegrand_le {m : ℕ} (z : Fin m → Pt) :
    ENNReal.ofReal (ckIntegrand m z) ≤ (boxM m).indicator (fun _ => ENNReal.ofReal ((m : ℝ) + 1)) z := by
  by_cases hc : (unitGraph (cfg z)).Connected
  · rw [indicator_of_mem (cfg_mem_boxM z hc)]
    apply ENNReal.ofReal_le_ofReal
    unfold ckIntegrand
    have hA := one_le_unionArea_cfg z
    have hp1 : unionArea (cfg z) ^ (-((m + 1 : ℝ) - 1 / 2)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hA (by linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)])
    have hp0 : 0 ≤ unionArea (cfg z) ^ (-((m + 1 : ℝ) - 1 / 2)) := Real.rpow_nonneg (by linarith) _
    have hg : dcG (unitGraph (cfg z)) ≤ (m : ℝ) + 1 := by
      have := dcG_le_card (unitGraph (cfg z))
      simpa using this
    rcases le_total 0 (dcG (unitGraph (cfg z))) with h0 | h0
    · nlinarith
    · nlinarith
  · have h0 : dcG (unitGraph (cfg z)) = 0 := by unfold dcG; rw [ite_eq_right hc]
    simp [ckIntegrand, h0]

theorem lintegral_ckIntegrand_lt_top (m : ℕ) : ∫⁻ z : Fin m → Pt, ENNReal.ofReal (ckIntegrand m z) < ⊤ := by
  have hB : MeasurableSet (boxM m) := MeasurableSet.univ_pi fun _ => measurableSet_Icc.prod measurableSet_Icc
  calc ∫⁻ z, ENNReal.ofReal (ckIntegrand m z)
      ≤ ∫⁻ z, (boxM m).indicator (fun _ => ENNReal.ofReal ((m : ℝ) + 1)) z := lintegral_mono fun z => ckIntegrand_le z
    _ = ENNReal.ofReal ((m : ℝ) + 1) * volume (boxM m) := lintegral_indicator_const hB _
    _ < ⊤ := by
        refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
        rw [boxM, volume_pi, Measure.pi_pi]
        refine ENNReal.prod_lt_top fun i _ => ?_
        rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Icc]
        exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top

/-- every `C_k` is finite -/
theorem cFinite : CFinite := by
  intro k _
  unfold C
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (lintegral_ckIntegrand_lt_top (k - 1))

end BHH.E

namespace BHH

-- the deliverables of this file, also under `BHH` (helpers stay in `BHH.E`)
export E (lintegral_ckIntegrand_lt_top cFinite)

end BHH
