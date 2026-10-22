/-
Module D: the interior term plus the extra terms of Prop 3.6 (`ExtraSpec`).

For one undetermined edge `p` (digit 2 of `idx3`): on the event "edge `p` present" the graph completes
`idx3 - 3^p`, on "absent" it completes `idx3 - 2·3^p`, so `2g ≥ gmin + Σ_σ (g_σ - gmin)⁺ 1_{F_σ}` on the box;
`PartitionBoundProp`, `EventBoundProp` per event and `ProbStripsProp` give the code's `singleLB` term.  For two
undetermined edges the four joint events are used, with `EdgeIndepProp` (vertex-disjoint pairs) or Fréchet.
-/
import BHH.LeafSound.Specs
import BHH.LeafSound.GraphState
import BHH.LeafSound.Digits

open BHH.Cert Real MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace BHH

namespace DX

/-! ## generic measure lemmas -/

lemma frechet' {α : Type*} [MeasurableSpace α] {μ : Measure α} {Q F₁ F₂ : Set α} (h1 : F₁ ⊆ Q) (h2 : F₂ ⊆ Q)
    (hm : MeasurableSet F₂) : μ F₁ + μ F₂ ≤ μ (F₁ ∩ F₂) + μ Q := by
  rw [← measure_union_add_inter₀ F₁ hm.nullMeasurableSet, add_comm (μ (F₁ ∪ F₂))]
  exact add_le_add le_rfl (measure_mono (Set.union_subset h1 h2))

/-- the Fréchet lower bound in the form used by the leaf -/
lemma frechet_ofReal {α : Type*} [MeasurableSpace α] {μ : Measure α} {Q F₁ F₂ : Set α} (h1 : F₁ ⊆ Q)
    (h2 : F₂ ⊆ Q) (hm : MeasurableSet F₂) (hQ : μ Q ≠ ⊤) {q₁ q₂ : ℝ}
    (hq₁ : ENNReal.ofReal (q₁ * (μ Q).toReal) ≤ μ F₁) (hq₂ : ENNReal.ofReal (q₂ * (μ Q).toReal) ≤ μ F₂) :
    ENNReal.ofReal (max (q₁ + q₂ - 1) 0 * (μ Q).toReal) ≤ μ (F₁ ∩ F₂) := by
  rcases le_total (q₁ + q₂ - 1) 0 with h | h
  · rw [max_eq_right h, zero_mul, ENNReal.ofReal_zero]; exact zero_le
  rw [max_eq_left h]
  have hF := frechet' (μ := μ) h1 h2 hm
  have hfin1 : μ F₁ ≠ ⊤ := ne_top_of_le_ne_top hQ (measure_mono h1)
  have hfin2 : μ F₂ ≠ ⊤ := ne_top_of_le_ne_top hQ (measure_mono h2)
  have hfin12 : μ (F₁ ∩ F₂) ≠ ⊤ := ne_top_of_le_ne_top hQ (measure_mono (inter_subset_left.trans h1))
  have hv : 0 ≤ (μ Q).toReal := ENNReal.toReal_nonneg
  -- real form
  have r1 : q₁ * (μ Q).toReal ≤ (μ F₁).toReal := by
    by_cases hq : 0 ≤ q₁ * (μ Q).toReal
    · exact (ENNReal.ofReal_le_iff_le_toReal hfin1).mp hq₁
    · exact le_trans (le_of_lt (not_le.mp hq)) ENNReal.toReal_nonneg
  have r2 : q₂ * (μ Q).toReal ≤ (μ F₂).toReal := by
    by_cases hq : 0 ≤ q₂ * (μ Q).toReal
    · exact (ENNReal.ofReal_le_iff_le_toReal hfin2).mp hq₂
    · exact le_trans (le_of_lt (not_le.mp hq)) ENNReal.toReal_nonneg
  have r3 : (μ F₁).toReal + (μ F₂).toReal ≤ (μ (F₁ ∩ F₂)).toReal + (μ Q).toReal := by
    rw [← ENNReal.toReal_add hfin1 hfin2, ← ENNReal.toReal_add hfin12 hQ]
    exact ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hfin12, hQ⟩) hF
  rw [ENNReal.ofReal_le_iff_le_toReal hfin12]
  nlinarith

/-- independence in the product form, with lower bounds `q₁ q₂ ≥ 0` -/
lemma indep_ofReal {α : Type*} [MeasurableSpace α] {μ : Measure α} {Q F₁ F₂ : Set α}
    {q₁ q₂ : ℝ} (hq₁ : 0 ≤ q₁) (hq₂ : 0 ≤ q₂) (hQ : μ Q ≠ ⊤) (h1Q : F₁ ⊆ Q) (h2Q : F₂ ⊆ Q)
    (hind : μ (F₁ ∩ F₂) * μ Q = μ F₁ * μ F₂)
    (h1 : ENNReal.ofReal (q₁ * (μ Q).toReal) ≤ μ F₁) (h2 : ENNReal.ofReal (q₂ * (μ Q).toReal) ≤ μ F₂) :
    ENNReal.ofReal (q₁ * q₂ * (μ Q).toReal) ≤ μ (F₁ ∩ F₂) := by
  rcases eq_or_ne (μ Q) 0 with h0 | h0
  · rw [h0, ENNReal.toReal_zero, mul_zero, ENNReal.ofReal_zero]; exact zero_le
  have hv : 0 < (μ Q).toReal := ENNReal.toReal_pos h0 hQ
  have hfin1 : μ F₁ ≠ ⊤ := ne_top_of_le_ne_top hQ (measure_mono h1Q)
  have hfin2 : μ F₂ ≠ ⊤ := ne_top_of_le_ne_top hQ (measure_mono h2Q)
  have hfin12 : μ (F₁ ∩ F₂) ≠ ⊤ := ne_top_of_le_ne_top hQ (measure_mono (inter_subset_left.trans h1Q))
  have r1 : q₁ * (μ Q).toReal ≤ (μ F₁).toReal := (ENNReal.ofReal_le_iff_le_toReal hfin1).mp h1
  have r2 : q₂ * (μ Q).toReal ≤ (μ F₂).toReal := (ENNReal.ofReal_le_iff_le_toReal hfin2).mp h2
  have r3 : (μ (F₁ ∩ F₂)).toReal * (μ Q).toReal = (μ F₁).toReal * (μ F₂).toReal := by
    rw [← ENNReal.toReal_mul, ← ENNReal.toReal_mul, hind]
  rw [ENNReal.ofReal_le_iff_le_toReal hfin12]
  have h12 : (q₁ * (μ Q).toReal) * (q₂ * (μ Q).toReal) ≤ (μ F₁).toReal * (μ F₂).toReal :=
    mul_le_mul r1 r2 (by positivity) ENNReal.toReal_nonneg
  have : q₁ * q₂ * (μ Q).toReal * (μ Q).toReal ≤ (μ (F₁ ∩ F₂)).toReal * (μ Q).toReal := by
    rw [r3]; nlinarith
  exact le_of_mul_le_mul_right this hv

/-- the `max · 0` form of Lemma 3.5 -/
lemma eventBound0 (hEv : EventBoundProp) {m : ℕ} {Q F : Set (Fin m → ℝ)} {f : (Fin m → ℝ) → ℝ≥0∞}
    {q fmin fmax V : ℝ} (hQ : MeasurableSet Q) (hF : MeasurableSet F) (hFQ : F ⊆ Q) (hQt : volume Q ≠ ⊤)
    (hq : 0 ≤ q) (hfmin0 : 0 ≤ fmin) (hfmax0 : 0 ≤ fmax)
    (hvol : ENNReal.ofReal (q * (volume Q).toReal) ≤ volume F)
    (hfl : ∀ x ∈ Q, ENNReal.ofReal fmin ≤ f x) (hfu : ∀ x ∈ Q, f x ≤ ENNReal.ofReal fmax)
    (hint : ENNReal.ofReal ((volume Q).toReal * V) ≤ ∫⁻ x in Q, f x) :
    ENNReal.ofReal ((volume Q).toReal * max (max (q * fmin) (V - (1 - q) * fmax)) 0) ≤ ∫⁻ x in F, f x := by
  rcases le_total (max (q * fmin) (V - (1 - q) * fmax)) 0 with h | h
  · rw [max_eq_right h, mul_zero, ENNReal.ofReal_zero]; exact zero_le
  · rw [max_eq_left h]
    exact hEv m Q F f q fmin fmax V hQ hF hFQ hQt hq hfmin0 hfmax0 hvol hfl hfu hint

/-- `E(q) = max(q fmin, V - (1 - q) fmax, 0)` -/
def EV (q fmin fmax V : ℝ) : ℝ := max (max (q * fmin) (V - (1 - q) * fmax)) 0

lemma EV_nonneg (q fmin fmax V : ℝ) : 0 ≤ EV q fmin fmax V := le_max_right _ _

/-- the core: partition bound plus Lemma 3.5 per event -/
theorem core (hEv : EventBoundProp) (hPB : PartitionBoundProp) {m : ℕ} {Q : Set (Fin m → ℝ)}
    (hQ : MeasurableSet Q) (hQt : volume Q ≠ ⊤)
    {f : (Fin m → ℝ) → ℝ≥0∞} {fmin fmax V g0 : ℝ} (hfmin0 : 0 ≤ fmin) (hfmax0 : 0 ≤ fmax) (hV0 : 0 ≤ V)
    (hg0 : 0 ≤ g0)
    (hfl : ∀ x ∈ Q, ENNReal.ofReal fmin ≤ f x) (hfu : ∀ x ∈ Q, f x ≤ ENNReal.ofReal fmax)
    (hint : ENNReal.ofReal ((volume Q).toReal * V) ≤ ∫⁻ x in Q, f x)
    {ι : Type} (S : Finset ι) (F : ι → Set (Fin m → ℝ)) (w q : ι → ℝ)
    (hFm : ∀ σ ∈ S, MeasurableSet (F σ)) (hFQ : ∀ σ ∈ S, F σ ⊆ Q) (hw : ∀ σ ∈ S, 0 ≤ w σ)
    (hq : ∀ σ ∈ S, 0 ≤ q σ)
    (hvol : ∀ σ ∈ S, ENNReal.ofReal (q σ * (volume Q).toReal) ≤ volume (F σ))
    (G : (Fin m → ℝ) → ℝ) (hG : ∀ x ∈ Q, g0 + ∑ σ ∈ S, w σ * (F σ).indicator (fun _ => (1 : ℝ)) x ≤ G x) :
    ENNReal.ofReal ((volume Q).toReal * (g0 * V + ∑ σ ∈ S, w σ * EV (q σ) fmin fmax V)) ≤
      ∫⁻ x in Q, ENNReal.ofReal (G x) * f x := by
  have hP := hPB m ι S Q F f G g0 w hQ hFm hFQ hg0 hw hG
  refine le_trans ?_ hP
  have hv : 0 ≤ (volume Q).toReal := ENNReal.toReal_nonneg
  have hE : ∀ σ ∈ S, ENNReal.ofReal ((volume Q).toReal * EV (q σ) fmin fmax V) ≤ ∫⁻ x in F σ, f x :=
    fun σ hσ => eventBound0 hEv hQ (hFm σ hσ) (hFQ σ hσ) hQt (hq σ hσ) hfmin0 hfmax0 (hvol σ hσ) hfl hfu hint
  have hsum0 : 0 ≤ (volume Q).toReal * ∑ σ ∈ S, w σ * EV (q σ) fmin fmax V :=
    mul_nonneg hv (Finset.sum_nonneg (fun σ hσ => mul_nonneg (hw σ hσ) (EV_nonneg _ _ _ _)))
  rw [mul_add, ENNReal.ofReal_add (by positivity) hsum0]
  apply add_le_add
  · rw [show (volume Q).toReal * (g0 * V) = g0 * ((volume Q).toReal * V) by ring, ENNReal.ofReal_mul hg0]
    gcongr
  · rw [Finset.mul_sum, ENNReal.ofReal_sum_of_nonneg (fun σ hσ =>
      mul_nonneg hv (mul_nonneg (hw σ hσ) (EV_nonneg _ _ _ _)))]
    apply Finset.sum_le_sum
    intro σ hσ
    rw [show (volume Q).toReal * (w σ * EV (q σ) fmin fmax V) = w σ * ((volume Q).toReal * EV (q σ) fmin fmax V)
      by ring, ENNReal.ofReal_mul (hw σ hσ)]
    gcongr
    exact hE σ hσ

/-! ## digits of modified edge states -/

lemma val3_set : ∀ (st : List ℕ) (p v : ℕ), p < st.length →
    val3 (st.set p v) + st.getD p 0 * 3 ^ p = val3 st + v * 3 ^ p
  | [], p, v, h => by simp at h
  | s :: rest, 0, v, _ => by simp only [List.set_cons_zero, val3, List.getD_cons_zero, pow_zero]; ring
  | s :: rest, p + 1, v, h => by
    simp only [List.set_cons_succ, val3, List.getD_cons_succ, pow_succ]
    have := val3_set rest p v (by simpa using h)
    nlinarith [this]

lemma val3_set_two {st : List ℕ} {p v : ℕ} (hp : p < st.length) (h2 : st.getD p 0 = 2) (hv : v ≤ 1) :
    val3 (st.set p v) = val3 st - (2 - v) * 3 ^ p := by
  have h := val3_set st p v hp
  rw [h2] at h
  interval_cases v <;> omega

lemma getD_set' (st : List ℕ) (p v q : ℕ) (hq : q < st.length) :
    (st.set p v).getD q 0 = if p = q then v else st.getD q 0 := by
  rw [List.getD_eq_getElem _ _ (by simpa using hq), List.getD_eq_getElem _ _ hq, List.getElem_set]

lemma set_lt3 {st : List ℕ} (hst : ∀ s ∈ st, s < 3) {p v : ℕ} (hv : v < 3) : ∀ s ∈ st.set p v, s < 3 := by
  intro s hs
  rcases List.mem_or_eq_of_mem_set hs with h | h
  · exact hst s h
  · omega

/-- setting digit `p` to the actual state of edge `p` keeps a completion -/
lemma completes_set {k : ℕ} {st : List ℕ} (hst : ∀ s ∈ st, s < 3) (hlen : st.length = (pairList k).length)
    {e : ℕ} (hc : Completes k (val3 st) e) {p v : ℕ} (hp : p < st.length) (hv : v < 3)
    (h1 : v = 1 → e.testBit p) (h0 : v = 0 → ¬ e.testBit p) : Completes k (val3 (st.set p v)) e := by
  refine ⟨hc.1, fun q hq => ?_⟩
  have hql : q < st.length := by rw [hlen]; exact hq
  have hd := val3_digit (st.set p v) (set_lt3 hst hv) q (by rw [List.length_set]; exact hql)
  rw [hd, getD_set' st p v q hql]
  split_ifs with hpq
  · subst hpq; exact ⟨h1, h0⟩
  · have := hc.2 q hq
    rwa [val3_digit st hst q hql] at this

lemma gmin_le_of_completes {k : ℕ} {gt : GTab} (hgt : GTabSound k gt) {st : List ℕ} (hst : ∀ s ∈ st, s < 3)
    (hlen : st.length = (pairList k).length) {y : Fin k → Pt} (hc : Completes k (val3 st) (edgeBits k y)) :
    (gt.gmin (val3 st) : ℝ) ≤ 2 * dcG (unitGraph y) := by
  have h := hgt _ _ (by have := val3_lt3 st hst; rwa [hlen] at this) hc
  rwa [graphOf_edgeBits] at h

/-! ## code facts -/

lemma mem_probsOf {bx : List PtBox} {pairs : List (ℕ × ℕ)} {st : List ℕ} {e : ℕ × ℕ × ℕ × (ℤ × ℤ)}
    (he : e ∈ probsOf bx pairs st) :
    ∃ p, p < pairs.length ∧ st.getD p 0 = 2 ∧
      e = (p, (pairs.getD p (0, 0)).1, (pairs.getD p (0, 0)).2,
        probStrips (bx.getD (pairs.getD p (0, 0)).1 default) (bx.getD (pairs.getD p (0, 0)).2 default)) := by
  unfold probsOf at he
  simp only [List.mem_map, List.mem_filter, List.mem_range, beq_iff_eq] at he
  obtain ⟨p, ⟨hp, h2⟩, rfl⟩ := he
  exact ⟨p, hp, h2, rfl⟩

lemma probStrips_nonneg (P Q : PtBox) : 0 ≤ (probStrips P Q).1 ∧ 0 ≤ (probStrips P Q).2 := by
  unfold probStrips
  dsimp only
  by_cases hw : (P.xh - Q.xl) - (P.xl - Q.xh) ≤ 0
  · rw [if_pos hw]; exact ⟨le_refl _, le_refl _⟩
  · rw [if_neg hw]; exact ⟨le_max_right _ _, le_max_right _ _⟩

lemma fx_mul_le_shrU' (x y : ℤ) : fx x * fx y ≤ fx (shrU (x * y) PR) := by
  have h := le_shrU (x * y) PR
  unfold fx
  calc (x : ℝ) / 2 ^ PR * ((y : ℝ) / 2 ^ PR) = ((x * y : ℤ) : ℝ) / 2 ^ PR / 2 ^ PR := by push_cast; ring
    _ ≤ ((shrU (x * y) PR : ℤ) : ℝ) / 2 ^ PR := by gcongr

lemma fx_shrD_le (x y : ℤ) : fx (shrD (x * y) PR) ≤ fx x * fx y := by
  have h := shrD_le (x * y) PR
  unfold fx
  calc ((shrD (x * y) PR : ℤ) : ℝ) / 2 ^ PR ≤ ((x * y : ℤ) : ℝ) / 2 ^ PR / 2 ^ PR := by gcongr
    _ = (x : ℝ) / 2 ^ PR * ((y : ℝ) / 2 ^ PR) := by push_cast; ring

lemma fx_max'' (a b : ℤ) : fx (max a b) = max (fx a) (fx b) := by
  rcases le_total a b with h | h
  · rw [max_eq_right h, max_eq_right (by unfold fx; gcongr)]
  · rw [max_eq_left h, max_eq_left (by unfold fx; gcongr)]

lemma fx_zero' : fx 0 = 0 := by simp [fx]
lemma fx_ONE' : fx ONE = 1 := by unfold fx; rw [ONE_cast]; exact div_self (by positivity)
lemma fx_sub'' (a b : ℤ) : fx (a - b) = fx a - fx b := by unfold fx; push_cast; ring
lemma fx_add'' (a b : ℤ) : fx (a + b) = fx a + fx b := by unfold fx; push_cast; ring
lemma fx_mul_int'' (n a : ℤ) : fx (n * a) = n * fx a := by unfold fx; push_cast; ring

/-- the code's `evLB` is at most `EV` of the real values -/
lemma fx_evLB_le (q fminLo fmaxHi val : ℤ) :
    fx (evLB q fminLo fmaxHi val) ≤ EV (fx q) (fx fminLo) (fx fmaxHi) (fx val) := by
  unfold evLB EV
  rw [fx_max'', fx_max'', fx_zero']
  apply max_le_max _ le_rfl
  apply max_le_max (fx_shrD_le q fminLo)
  rw [fx_sub'']
  have h := fx_mul_le_shrU' (ONE - q) fmaxHi
  rw [fx_sub'', fx_ONE'] at h
  linarith

/-- the score term `(g - gmin)⁺ · evLB` -/
lemma fx_score_le (g gmin : ℤ) (ev : ℤ) {E : ℝ} (hE : fx ev ≤ E) (hE0 : 0 ≤ E) :
    fx (if gmin < g then (g - gmin) * ev else 0) ≤ max ((g - gmin : ℤ) : ℝ) 0 * E := by
  split_ifs with h
  · rw [fx_mul_int'', max_eq_left (by exact_mod_cast (sub_pos.mpr h).le)]
    exact mul_le_mul_of_nonneg_left hE (by exact_mod_cast (sub_pos.mpr h).le)
  · rw [fx_zero']; exact mul_nonneg (le_max_right _ _) hE0


/-! ## the box and the edge events -/

lemma measurableSet_boxOf' {m : ℕ} (lo hi : List ℤ) : MeasurableSet (boxOf lo hi : Set (Fin m → ℝ)) :=
  MeasurableSet.univ_pi fun _ => measurableSet_Ico

lemma volume_boxOf_ne_top' {m : ℕ} (lo hi : List ℤ) : volume (boxOf lo hi : Set (Fin m → ℝ)) ≠ ⊤ := by
  unfold boxOf
  rw [volume_pi, Measure.pi_pi]
  exact ENNReal.prod_ne_top fun d _ => by rw [Real.volume_Ico]; exact ENNReal.ofReal_ne_top

lemma continuous_xget {m : ℕ} (d : ℕ) : Continuous fun x : Fin m → ℝ => xget x d := by
  unfold xget
  by_cases h : d < m
  · simp only [h, dite_true]; exact continuous_apply _
  · simp only [h, dite_false]; exact continuous_const

lemma continuous_xcfg' {k : ℕ} (i : Fin k) : Continuous fun x : Fin (mDim k) → ℝ => xcfg k x i := by
  unfold xcfg
  split_ifs
  · exact continuous_const
  · exact (continuous_xget 0).prodMk continuous_const
  · exact (continuous_xget _).prodMk (continuous_xget _)

lemma continuous_pairSq' {k : ℕ} (i j : Fin k) :
    Continuous fun x : Fin (mDim k) → ℝ => sqDist (xcfg k x i) (xcfg k x j) := by
  unfold sqDist
  have hi := continuous_xcfg' (k := k) i
  have hj := continuous_xcfg' (k := k) j
  fun_prop

/-- the event "edge `ij` present" (`b = true`) or "absent" (`b = false`) on the box -/
def edgeEv (k : ℕ) (lo hi : List ℤ) (i j : Fin k) (b : Bool) : Set (Fin (mDim k) → ℝ) :=
  if b then {x ∈ (boxOf lo hi : Set (Fin (mDim k) → ℝ)) | sqDist (xcfg k x i) (xcfg k x j) ≤ 1}
  else {x ∈ (boxOf lo hi : Set (Fin (mDim k) → ℝ)) | 1 < sqDist (xcfg k x i) (xcfg k x j)}

lemma edgeEv_sub {k : ℕ} (lo hi : List ℤ) (i j : Fin k) (b : Bool) :
    edgeEv k lo hi i j b ⊆ (boxOf lo hi : Set (Fin (mDim k) → ℝ)) := by
  unfold edgeEv; cases b <;> exact fun x hx => hx.1

lemma edgeEv_meas {k : ℕ} (lo hi : List ℤ) (i j : Fin k) (b : Bool) : MeasurableSet (edgeEv k lo hi i j b) := by
  unfold edgeEv
  cases b
  · exact (measurableSet_boxOf' lo hi).inter
      (measurableSet_lt measurable_const (continuous_pairSq' i j).measurable)
  · exact (measurableSet_boxOf' lo hi).inter
      (measurableSet_le (continuous_pairSq' i j).measurable measurable_const)

lemma mem_edgeEv {k : ℕ} {lo hi : List ℤ} {i j : Fin k} {b : Bool} {x : Fin (mDim k) → ℝ}
    (hx : x ∈ (boxOf lo hi : Set (Fin (mDim k) → ℝ))) :
    x ∈ edgeEv k lo hi i j b ↔ (decide (sqDist (xcfg k x i) (xcfg k x j) ≤ 1) = b) := by
  unfold edgeEv
  cases b <;> simp [hx]

/-- the actual state of the edge `p` and the completion with digit `p` set to it -/
lemma g_ge_set {k : ℕ} (hk3 : 3 ≤ k) {gt : GTab} (hgt : GTabSound k gt) {lo hi : List ℤ}
    {x : Fin (mDim k) → ℝ} (hx : x ∈ (boxOf lo hi : Set (Fin (mDim k) → ℝ))) {p : ℕ}
    (hp : p < (pairList k).length) (h2 : (stCode k lo hi).getD p 0 = 2) (b : Bool)
    (hb : decide (sqDist (xcfg k x ⟨((pairList k)[p]).1, lt_trans (pairList_get_lt hp).1 (pairList_get_lt hp).2⟩)
      (xcfg k x ⟨((pairList k)[p]).2, (pairList_get_lt hp).2⟩) ≤ 1) = b) :
    (gt.gmin (val3 (stCode k lo hi) - (if b then pow3 p else 2 * pow3 p)) : ℝ) ≤
      2 * dcG (unitGraph (xcfg k x)) := by
  set st := stCode k lo hi with hst
  have hlen : st.length = (pairList k).length := stCode_length k lo hi
  have hpl : p < st.length := by rw [hlen]; exact hp
  have hc := completes_stCode hk3 hx
  have hik := lt_trans (pairList_get_lt hp).1 (pairList_get_lt hp).2
  have hjk := (pairList_get_lt hp).2
  have htb : (edgeBits k (xcfg k x)).testBit p ↔
      sqDist (xcfg k x ⟨((pairList k)[p]).1, hik⟩) (xcfg k x ⟨((pairList k)[p]).2, hjk⟩) ≤ 1 := by
    rw [edgeBits_testBit k _ hp]
    simp [ptN, hik, hjk]
  have hv : (if b then 1 else 0) < 3 := by split_ifs <;> norm_num
  have hc' := completes_set (stCode_lt3 k lo hi) hlen hc hpl hv
    (fun h => by cases b <;> simp_all) (fun h => by cases b <;> simp_all)
  have hg := gmin_le_of_completes hgt (set_lt3 (stCode_lt3 k lo hi) hv) (by rw [List.length_set]; exact hlen) hc'
  have he : val3 (st.set p (if b then 1 else 0)) = val3 st - (if b then pow3 p else 2 * pow3 p) := by
    rw [val3_set_two hpl h2 (by split_ifs <;> norm_num)]
    unfold pow3
    cases b <;> simp
  rwa [he] at hg

/-! ## one undetermined edge -/

/-- the code's score for one undetermined edge -/
def scSingle (gt : GTab) (idx3 : ℕ) (gmin fminLo fmaxHi val : ℤ) (e : ℕ × ℕ × ℕ × (ℤ × ℤ)) : ℤ :=
  (if gmin < gt.gmin (idx3 - pow3 e.1) then (gt.gmin (idx3 - pow3 e.1) - gmin) * evLB e.2.2.2.1 fminLo fmaxHi val
    else 0) +
  (if gmin < gt.gmin (idx3 - 2 * pow3 e.1) then
      (gt.gmin (idx3 - 2 * pow3 e.1) - gmin) * evLB e.2.2.2.2 fminLo fmaxHi val else 0)

lemma singleLB_eq (gt : GTab) (idx3 : ℕ) (gmin : ℤ) (probs : List (ℕ × ℕ × ℕ × (ℤ × ℤ))) (fminLo fmaxHi val : ℤ) :
    singleLB gt idx3 gmin probs fminLo fmaxHi val =
      probs.foldl (fun best e => max best (scSingle gt idx3 gmin fminLo fmaxHi val e)) 0 := by
  unfold singleLB
  congr 1

lemma foldl_max_cases {α : Type*} (g : α → ℤ) : ∀ (L : List α) (b : ℤ),
    L.foldl (fun best e => max best (g e)) b = b ∨ ∃ e ∈ L, L.foldl (fun best e => max best (g e)) b = g e
  | [], b => Or.inl rfl
  | e :: L, b => by
    simp only [List.foldl_cons]
    rcases foldl_max_cases g L (max b (g e)) with h | ⟨e', he', h⟩
    · rcases le_total b (g e) with hbe | hbe
      · rw [max_eq_right hbe] at h ⊢; exact Or.inr ⟨e, List.mem_cons_self, h⟩
      · rw [max_eq_left hbe] at h ⊢; exact Or.inl h
    · exact Or.inr ⟨e', List.mem_cons_of_mem _ he', h⟩


/-- the bound for one undetermined edge -/
theorem single_le {k : ℕ} (hk3 : 3 ≤ k) {gt : GTab} (hgt : GTabSound k gt) (hEv : EventBoundProp)
    (hPB : PartitionBoundProp) (hPS : ProbStripsProp) {lo hi : List ℤ} (hv : ValidBox k lo hi)
    {f : (Fin (mDim k) → ℝ) → ℝ≥0∞} {fminLo fmaxHi val : ℤ} (hfmin0 : 0 ≤ fminLo) (hfmax0 : 0 ≤ fmaxHi)
    (hval0 : 0 ≤ val)
    (hfl : ∀ x ∈ (boxOf lo hi : Set (Fin (mDim k) → ℝ)), ENNReal.ofReal (fx fminLo) ≤ f x)
    (hfu : ∀ x ∈ (boxOf lo hi : Set (Fin (mDim k) → ℝ)), f x ≤ ENNReal.ofReal (fx fmaxHi))
    (hint : ENNReal.ofReal ((volume (boxOf lo hi : Set (Fin (mDim k) → ℝ))).toReal * fx val) ≤
      ∫⁻ x in boxOf lo hi, f x)
    (hg0 : 0 ≤ gt.gmin (val3 (stCode k lo hi)))
    {e : ℕ × ℕ × ℕ × (ℤ × ℤ)} (he : e ∈ probsOf (ptBoxes k lo hi) (pairList k) (stCode k lo hi)) :
    ENNReal.ofReal ((volume (boxOf lo hi : Set (Fin (mDim k) → ℝ))).toReal *
        ((gt.gmin (val3 (stCode k lo hi)) : ℝ) * fx val +
          fx (scSingle gt (val3 (stCode k lo hi)) (gt.gmin (val3 (stCode k lo hi))) fminLo fmaxHi val e))) ≤
      ∫⁻ x in boxOf lo hi, ENNReal.ofReal (2 * dcG (unitGraph (xcfg k x))) * f x := by
  obtain ⟨p, hp, h2, rfl⟩ := mem_probsOf he
  have hgetD : (pairList k).getD p (0, 0) = (pairList k)[p] := List.getD_eq_getElem _ _ hp
  obtain ⟨hij, hjk⟩ := pairList_get_lt hp
  have hik := lt_trans hij hjk
  rw [hgetD]
  set i : Fin k := ⟨((pairList k)[p]).1, hik⟩ with hi_def
  set j : Fin k := ⟨((pairList k)[p]).2, hjk⟩ with hj_def
  set gmin := gt.gmin (val3 (stCode k lo hi)) with hgmin_def
  set idx3 := val3 (stCode k lo hi) with hidx3
  set PSv := probStrips ((ptBoxes k lo hi).getD i.val default) ((ptBoxes k lo hi).getD j.val default) with hPSv
  set gp := gt.gmin (idx3 - pow3 p) with hgp_def
  set ga := gt.gmin (idx3 - 2 * pow3 p) with hga_def
  have hfmin0' : (0 : ℝ) ≤ fx fminLo := by unfold fx; positivity
  have hfmax0' : (0 : ℝ) ≤ fx fmaxHi := by unfold fx; positivity
  have hV0 : (0 : ℝ) ≤ fx val := by unfold fx; positivity
  have hg0' : (0 : ℝ) ≤ gmin := by exact_mod_cast hg0
  obtain ⟨hq1, hq2⟩ := probStrips_nonneg ((ptBoxes k lo hi).getD i.val default) ((ptBoxes k lo hi).getD j.val default)
  have hcore := core hEv hPB (measurableSet_boxOf' lo hi) (volume_boxOf_ne_top' lo hi) hfmin0' hfmax0' hV0 hg0'
    hfl hfu hint (Finset.univ : Finset Bool) (edgeEv k lo hi i j)
    (fun b => if b then max ((gp - gmin : ℤ) : ℝ) 0 else max ((ga - gmin : ℤ) : ℝ) 0)
    (fun b => if b then fx PSv.1 else fx PSv.2)
    (fun b _ => edgeEv_meas lo hi i j b) (fun b _ => edgeEv_sub lo hi i j b)
    (fun b _ => by cases b <;> simp)
    (fun b _ => by
      cases b
      · show (0 : ℝ) ≤ fx PSv.2
        unfold fx; exact div_nonneg (by exact_mod_cast hq2) (by positivity)
      · show (0 : ℝ) ≤ fx PSv.1
        unfold fx; exact div_nonneg (by exact_mod_cast hq1) (by positivity))
    (fun b _ => by
      obtain ⟨r1, r2⟩ := hPS k lo hi hv i j (Fin.lt_def.mpr hij)
      cases b
      · show ENNReal.ofReal (fx PSv.2 * _) ≤
          volume {x ∈ (boxOf lo hi : Set (Fin (mDim k) → ℝ)) | 1 < sqDist (xcfg k x i) (xcfg k x j)}
        exact r2
      · show ENNReal.ofReal (fx PSv.1 * _) ≤
          volume {x ∈ (boxOf lo hi : Set (Fin (mDim k) → ℝ)) | sqDist (xcfg k x i) (xcfg k x j) ≤ 1}
        exact r1)
    (fun x => 2 * dcG (unitGraph (xcfg k x)))
    (by
      intro x hx
      rw [Fintype.sum_bool]
      have hgm := gmin_le_two_g hk3 hgt hx
      by_cases hpres : sqDist (xcfg k x i) (xcfg k x j) ≤ 1
      · have h1 : x ∈ edgeEv k lo hi i j true := (mem_edgeEv hx).mpr (decide_eq_true hpres)
        have h0 : x ∉ edgeEv k lo hi i j false := fun h => by
          have := (mem_edgeEv hx).mp h; rw [decide_eq_false_iff_not] at this; exact this hpres
        rw [Set.indicator_of_mem h1, Set.indicator_of_notMem h0]
        have hgp := g_ge_set hk3 hgt hx hp h2 true (decide_eq_true hpres)
        simp only [ite_true, mul_one, mul_zero, add_zero, Bool.false_eq_true, ite_false] at hgp ⊢
        rcases le_total ((gp - gmin : ℤ) : ℝ) 0 with hc | hc
        · rw [max_eq_right hc]; linarith
        · rw [max_eq_left hc]; push_cast; linarith
      · have h0 : x ∈ edgeEv k lo hi i j false := (mem_edgeEv hx).mpr (decide_eq_false hpres)
        have h1 : x ∉ edgeEv k lo hi i j true := fun h => by
          have := (mem_edgeEv hx).mp h; rw [decide_eq_true_iff] at this; exact hpres this
        rw [Set.indicator_of_mem h0, Set.indicator_of_notMem h1]
        have hga := g_ge_set hk3 hgt hx hp h2 false (decide_eq_false hpres)
        simp only [ite_true, mul_one, mul_zero, zero_add, Bool.false_eq_true, ite_false] at hga ⊢
        rcases le_total ((ga - gmin : ℤ) : ℝ) 0 with hc | hc
        · rw [max_eq_right hc]; linarith
        · rw [max_eq_left hc]; push_cast; linarith)
  refine le_trans (ENNReal.ofReal_le_ofReal ?_) hcore
  apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
  apply add_le_add le_rfl
  rw [Fintype.sum_bool]
  simp only [ite_true, Bool.false_eq_true, ite_false]
  unfold scSingle
  rw [fx_add'']
  exact add_le_add (fx_score_le _ _ _ (fx_evLB_le _ _ _ _) (EV_nonneg _ _ _ _))
    (fx_score_le _ _ _ (fx_evLB_le _ _ _ _) (EV_nonneg _ _ _ _))


/-! ## two undetermined edges: the code -/

/-- the code's score for two undetermined edges -/
def scPair (gt : GTab) (idx3 : ℕ) (gmin fminLo fmaxHi val : ℤ) (e1 e2 : ℕ × ℕ × ℕ × (ℤ × ℤ)) : ℤ :=
  [((1 : ℕ), (1 : ℕ)), (1, 0), (0, 1), (0, 0)].foldl (fun acc (s : ℕ × ℕ) =>
    if gt.gmin (idx3 - (if s.1 == 1 then pow3 e1.1 else 2 * pow3 e1.1)
        - (if s.2 == 1 then pow3 e2.1 else 2 * pow3 e2.1)) ≤ gmin then acc
    else acc + (gt.gmin (idx3 - (if s.1 == 1 then pow3 e1.1 else 2 * pow3 e1.1)
        - (if s.2 == 1 then pow3 e2.1 else 2 * pow3 e2.1)) - gmin) *
      evLB (if (e1.2.1 != e2.2.1 ∧ e1.2.1 != e2.2.2.1 ∧ e1.2.2.1 != e2.2.1 ∧ e1.2.2.1 != e2.2.2.1) then
          shrD ((if s.1 == 1 then e1.2.2.2.1 else e1.2.2.2.2) * (if s.2 == 1 then e2.2.2.2.1 else e2.2.2.2.2)) PR
        else Max.max ((if s.1 == 1 then e1.2.2.2.1 else e1.2.2.2.2) +
          (if s.2 == 1 then e2.2.2.2.1 else e2.2.2.2.2) - ONE) 0) fminLo fmaxHi val) 0

lemma pairsLB_eq (gt : GTab) (idx3 : ℕ) (gmin : ℤ) (probs : List (ℕ × ℕ × ℕ × (ℤ × ℤ))) (fminLo fmaxHi val : ℤ) :
    pairsLB gt idx3 gmin probs fminLo fmaxHi val =
      probs.foldl (fun best e1 => probs.foldl (fun best2 e2 =>
        if e1.1 < e2.1 then max best2 (scPair gt idx3 gmin fminLo fmaxHi val e1 e2) else best2) best) 0 := by
  unfold pairsLB
  congr 1

lemma foldl_inner_cases {α : Type*} (L : List α) (c : α → Prop) [DecidablePred c] (h : α → ℤ) :
    ∀ (M : List α) (b : ℤ), (∀ e ∈ M, e ∈ L) →
      M.foldl (fun best2 e2 => if c e2 then max best2 (h e2) else best2) b = b ∨
      ∃ e2 ∈ L, c e2 ∧ M.foldl (fun best2 e2 => if c e2 then max best2 (h e2) else best2) b = h e2
  | [], b, _ => Or.inl rfl
  | e :: M, b, hM => by
    simp only [List.foldl_cons]
    have hM' : ∀ e' ∈ M, e' ∈ L := fun e' he' => hM e' (List.mem_cons_of_mem _ he')
    split_ifs with hc
    · rcases foldl_inner_cases L c h M (max b (h e)) hM' with h1 | ⟨e2, he2, hc2, h1⟩
      · rcases le_total b (h e) with hbe | hbe
        · rw [max_eq_right hbe] at h1 ⊢; exact Or.inr ⟨e, hM e List.mem_cons_self, hc, h1⟩
        · rw [max_eq_left hbe] at h1 ⊢; exact Or.inl h1
      · exact Or.inr ⟨e2, he2, hc2, h1⟩
    · exact foldl_inner_cases L c h M b hM'

lemma foldl_pairs_cases {α : Type*} (L : List α) (c : α → α → Prop) [∀ a b, Decidable (c a b)]
    (h : α → α → ℤ) : ∀ (M : List α) (b : ℤ), (∀ e ∈ M, e ∈ L) →
      M.foldl (fun best e1 => L.foldl (fun best2 e2 => if c e1 e2 then max best2 (h e1 e2) else best2) best) b
        = b ∨ ∃ e1 ∈ L, ∃ e2 ∈ L, c e1 e2 ∧
      M.foldl (fun best e1 => L.foldl (fun best2 e2 => if c e1 e2 then max best2 (h e1 e2) else best2) best) b
        = h e1 e2
  | [], b, _ => Or.inl rfl
  | e1 :: M, b, hM => by
    simp only [List.foldl_cons]
    have hM' : ∀ e' ∈ M, e' ∈ L := fun e' he' => hM e' (List.mem_cons_of_mem _ he')
    set b' := L.foldl (fun best2 e2 => if c e1 e2 then max best2 (h e1 e2) else best2) b with hb'
    rcases foldl_pairs_cases L c h M b' hM' with h1 | ⟨e1', he1', e2', he2', hc', h1⟩
    · rcases foldl_inner_cases L (c e1) (h e1) L b (fun e he => he) with h2 | ⟨e2, he2, hc2, h2⟩
      · rw [h1, hb', h2]; exact Or.inl rfl
      · rw [h1, hb', h2]; exact Or.inr ⟨e1, hM e1 List.mem_cons_self, e2, he2, hc2, rfl⟩
    · exact Or.inr ⟨e1', he1', e2', he2', hc', h1⟩

lemma foldl_ite_sum {β : Type*} (c : β → Prop) [DecidablePred c] (t : β → ℤ) :
    ∀ (L : List β) (a : ℤ), L.foldl (fun acc s => if c s then acc else acc + t s) a =
      a + (L.map fun s => if c s then 0 else t s).sum
  | [], a => by simp
  | s :: L, a => by
    simp only [List.foldl_cons, List.map_cons, List.sum_cons]
    rw [foldl_ite_sum c t L]
    split_ifs <;> ring

/-- the variant `if g ≤ gmin then 0 else (g - gmin) ev` of `fx_score_le` -/
lemma fx_score_le' (g gmin : ℤ) (ev : ℤ) {E : ℝ} (hE : fx ev ≤ E) (hE0 : 0 ≤ E) :
    fx (if g ≤ gmin then 0 else (g - gmin) * ev) ≤ max ((g - gmin : ℤ) : ℝ) 0 * E := by
  have := fx_score_le g gmin ev hE hE0
  by_cases h : g ≤ gmin
  · rw [if_pos h, fx_zero']; exact mul_nonneg (le_max_right _ _) hE0
  · rw [if_neg h]; rw [if_pos (not_le.mp h)] at this; exact this

/-! ## two undetermined edges: the completions -/

lemma g_ge_set2 {k : ℕ} (hk3 : 3 ≤ k) {gt : GTab} (hgt : GTabSound k gt) {lo hi : List ℤ}
    {x : Fin (mDim k) → ℝ} (hx : x ∈ (boxOf lo hi : Set (Fin (mDim k) → ℝ))) {p1 p2 : ℕ}
    (hp1 : p1 < (pairList k).length) (hp2 : p2 < (pairList k).length) (hne : p1 ≠ p2)
    (h21 : (stCode k lo hi).getD p1 0 = 2) (h22 : (stCode k lo hi).getD p2 0 = 2) (b1 b2 : Bool)
    (hb1 : decide (sqDist (xcfg k x ⟨((pairList k)[p1]).1,
        lt_trans (pairList_get_lt hp1).1 (pairList_get_lt hp1).2⟩)
      (xcfg k x ⟨((pairList k)[p1]).2, (pairList_get_lt hp1).2⟩) ≤ 1) = b1)
    (hb2 : decide (sqDist (xcfg k x ⟨((pairList k)[p2]).1,
        lt_trans (pairList_get_lt hp2).1 (pairList_get_lt hp2).2⟩)
      (xcfg k x ⟨((pairList k)[p2]).2, (pairList_get_lt hp2).2⟩) ≤ 1) = b2) :
    (gt.gmin (val3 (stCode k lo hi) - (if b1 then pow3 p1 else 2 * pow3 p1)
      - (if b2 then pow3 p2 else 2 * pow3 p2)) : ℝ) ≤ 2 * dcG (unitGraph (xcfg k x)) := by
  set st := stCode k lo hi with hst
  have hlen : st.length = (pairList k).length := stCode_length k lo hi
  have hpl1 : p1 < st.length := by rw [hlen]; exact hp1
  have hpl2 : p2 < st.length := by rw [hlen]; exact hp2
  have hc := completes_stCode hk3 hx
  have htb : ∀ p (hp : p < (pairList k).length), (edgeBits k (xcfg k x)).testBit p ↔
      sqDist (xcfg k x ⟨((pairList k)[p]).1, lt_trans (pairList_get_lt hp).1 (pairList_get_lt hp).2⟩)
        (xcfg k x ⟨((pairList k)[p]).2, (pairList_get_lt hp).2⟩) ≤ 1 := by
    intro p hp
    have hik := lt_trans (pairList_get_lt hp).1 (pairList_get_lt hp).2
    have hjk := (pairList_get_lt hp).2
    rw [edgeBits_testBit k _ hp]
    simp [ptN, hik, hjk]
  have hv1 : (if b1 then 1 else 0) < 3 := by split_ifs <;> norm_num
  have hv2 : (if b2 then 1 else 0) < 3 := by split_ifs <;> norm_num
  have hc1 := completes_set (stCode_lt3 k lo hi) hlen hc hpl1 hv1
    (fun h => by have := (htb p1 hp1).mpr; cases b1 <;> simp_all) (fun h => by
      have := (htb p1 hp1).mp; cases b1 <;> simp_all)
  have hst1 := set_lt3 (stCode_lt3 k lo hi) hv1 (p := p1)
  have hlen1 : (st.set p1 (if b1 then 1 else 0)).length = (pairList k).length := by
    rw [List.length_set]; exact hlen
  have hpl2' : p2 < (st.set p1 (if b1 then 1 else 0)).length := by rw [List.length_set]; exact hpl2
  have hc2 := completes_set hst1 hlen1 hc1 hpl2' hv2
    (fun h => by have := (htb p2 hp2).mpr; cases b2 <;> simp_all) (fun h => by
      have := (htb p2 hp2).mp; cases b2 <;> simp_all)
  have hg := gmin_le_of_completes hgt (set_lt3 hst1 hv2) (by rw [List.length_set]; exact hlen1) hc2
  have h22' : (st.set p1 (if b1 then 1 else 0)).getD p2 0 = 2 := by
    rw [getD_set' st p1 _ p2 hpl2, if_neg hne]; exact h22
  have he : val3 ((st.set p1 (if b1 then 1 else 0)).set p2 (if b2 then 1 else 0)) =
      val3 st - (if b1 then pow3 p1 else 2 * pow3 p1) - (if b2 then pow3 p2 else 2 * pow3 p2) := by
    rw [val3_set_two hpl2' h22' (by split_ifs <;> norm_num), val3_set_two hpl1 h21 (by split_ifs <;> norm_num)]
    unfold pow3
    cases b1 <;> cases b2 <;> simp
  rwa [he] at hg


/-! ## two undetermined edges: the bound -/

lemma edgeEv_eq_sep {k : ℕ} (lo hi : List ℤ) (i j : Fin k) (b : Bool) :
    {x ∈ (boxOf lo hi : Set (Fin (mDim k) → ℝ)) | sqDist (xcfg k x i) (xcfg k x j) ∈
      (if b then Iic (1 : ℝ) else Ioi 1)} = edgeEv k lo hi i j b := by
  unfold edgeEv; cases b <;> ext x <;> simp

lemma measurableSet_S (b : Bool) : MeasurableSet (if b then Iic (1 : ℝ) else Ioi 1) := by
  cases b
  · exact measurableSet_Ioi
  · exact measurableSet_Iic

lemma probEv {k : ℕ} (hPS : ProbStripsProp) {lo hi : List ℤ} (hv : ValidBox k lo hi) {i j : Fin k} (hij : i < j)
    (b : Bool) :
    ENNReal.ofReal ((if b then fx (probStrips ((ptBoxes k lo hi).getD i.val default)
        ((ptBoxes k lo hi).getD j.val default)).1
      else fx (probStrips ((ptBoxes k lo hi).getD i.val default) ((ptBoxes k lo hi).getD j.val default)).2) *
        (volume (boxOf lo hi : Set (Fin (mDim k) → ℝ))).toReal) ≤ volume (edgeEv k lo hi i j b) := by
  obtain ⟨r1, r2⟩ := hPS k lo hi hv i j hij
  cases b
  · exact r2
  · exact r1

lemma fx_nonneg_of {a : ℤ} (h : 0 ≤ a) : (0 : ℝ) ≤ fx a := by unfold fx; positivity

lemma mem_inter_edgeEv {k : ℕ} {lo hi : List ℤ} {i1 j1 i2 j2 : Fin k} {b1 b2 : Bool} {x : Fin (mDim k) → ℝ}
    (hx : x ∈ (boxOf lo hi : Set (Fin (mDim k) → ℝ))) :
    x ∈ edgeEv k lo hi i1 j1 b1 ∩ edgeEv k lo hi i2 j2 b2 ↔
      decide (sqDist (xcfg k x i1) (xcfg k x j1) ≤ 1) = b1 ∧ decide (sqDist (xcfg k x i2) (xcfg k x j2) ≤ 1) = b2 := by
  rw [mem_inter_iff, mem_edgeEv hx, mem_edgeEv hx]

theorem pair_le {k : ℕ} (hk3 : 3 ≤ k) {gt : GTab} (hgt : GTabSound k gt) (hEv : EventBoundProp)
    (hPB : PartitionBoundProp) (hPS : ProbStripsProp) (hEI : EdgeIndepProp) {lo hi : List ℤ}
    (hv : ValidBox k lo hi)
    {f : (Fin (mDim k) → ℝ) → ℝ≥0∞} {fminLo fmaxHi val : ℤ} (hfmin0 : 0 ≤ fminLo) (hfmax0 : 0 ≤ fmaxHi)
    (hval0 : 0 ≤ val)
    (hfl : ∀ x ∈ (boxOf lo hi : Set (Fin (mDim k) → ℝ)), ENNReal.ofReal (fx fminLo) ≤ f x)
    (hfu : ∀ x ∈ (boxOf lo hi : Set (Fin (mDim k) → ℝ)), f x ≤ ENNReal.ofReal (fx fmaxHi))
    (hint : ENNReal.ofReal ((volume (boxOf lo hi : Set (Fin (mDim k) → ℝ))).toReal * fx val) ≤
      ∫⁻ x in boxOf lo hi, f x)
    (hg0 : 0 ≤ gt.gmin (val3 (stCode k lo hi)))
    {e1 e2 : ℕ × ℕ × ℕ × (ℤ × ℤ)} (he1 : e1 ∈ probsOf (ptBoxes k lo hi) (pairList k) (stCode k lo hi))
    (he2 : e2 ∈ probsOf (ptBoxes k lo hi) (pairList k) (stCode k lo hi)) (hlt : e1.1 < e2.1) :
    ENNReal.ofReal ((volume (boxOf lo hi : Set (Fin (mDim k) → ℝ))).toReal *
        ((gt.gmin (val3 (stCode k lo hi)) : ℝ) * fx val +
          fx (scPair gt (val3 (stCode k lo hi)) (gt.gmin (val3 (stCode k lo hi))) fminLo fmaxHi val e1 e2))) ≤
      ∫⁻ x in boxOf lo hi, ENNReal.ofReal (2 * dcG (unitGraph (xcfg k x))) * f x := by
  obtain ⟨p1, hp1, h21, rfl⟩ := mem_probsOf he1
  obtain ⟨p2, hp2, h22, rfl⟩ := mem_probsOf he2
  simp only at hlt
  have hne : p1 ≠ p2 := Nat.ne_of_lt hlt
  rw [List.getD_eq_getElem _ _ hp1, List.getD_eq_getElem _ _ hp2]
  obtain ⟨hij1, hjk1⟩ := pairList_get_lt hp1
  obtain ⟨hij2, hjk2⟩ := pairList_get_lt hp2
  set i1 : Fin k := ⟨((pairList k)[p1]).1, lt_trans hij1 hjk1⟩ with hi1
  set j1 : Fin k := ⟨((pairList k)[p1]).2, hjk1⟩ with hj1
  set i2 : Fin k := ⟨((pairList k)[p2]).1, lt_trans hij2 hjk2⟩ with hi2
  set j2 : Fin k := ⟨((pairList k)[p2]).2, hjk2⟩ with hj2
  set gmin := gt.gmin (val3 (stCode k lo hi)) with hgmin_def
  set idx3 := val3 (stCode k lo hi) with hidx3
  set PS1 := probStrips ((ptBoxes k lo hi).getD i1.val default) ((ptBoxes k lo hi).getD j1.val default) with hPS1
  set PS2 := probStrips ((ptBoxes k lo hi).getD i2.val default) ((ptBoxes k lo hi).getD j2.val default) with hPS2
  obtain ⟨hq11, hq12⟩ := probStrips_nonneg ((ptBoxes k lo hi).getD i1.val default)
    ((ptBoxes k lo hi).getD j1.val default)
  obtain ⟨hq21, hq22⟩ := probStrips_nonneg ((ptBoxes k lo hi).getD i2.val default)
    ((ptBoxes k lo hi).getD j2.val default)
  set Box := (boxOf lo hi : Set (Fin (mDim k) → ℝ)) with hBox
  have hQm : MeasurableSet Box := measurableSet_boxOf' lo hi
  have hQt : volume Box ≠ ⊤ := volume_boxOf_ne_top' lo hi
  set dj : Prop := ((pairList k)[p1].1 != (pairList k)[p2].1) = true ∧ ((pairList k)[p1].1 != (pairList k)[p2].2) = true ∧
      ((pairList k)[p1].2 != (pairList k)[p2].1) = true ∧ ((pairList k)[p1].2 != (pairList k)[p2].2) = true with hdj
  -- the code's lower bounds
  set qa : Bool → ℤ := fun b => if b then PS1.1 else PS1.2 with hqa
  set qb : Bool → ℤ := fun b => if b then PS2.1 else PS2.2 with hqb
  have hqa0 : ∀ b, 0 ≤ qa b := fun b => by cases b; exact hq12; exact hq11
  have hqb0 : ∀ b, 0 ≤ qb b := fun b => by cases b; exact hq22; exact hq21
  set qc : Bool × Bool → ℤ := fun b => if dj then shrD (qa b.1 * qb b.2) PR else max (qa b.1 + qb b.2 - ONE) 0
    with hqc
  set gs : Bool × Bool → ℤ := fun b => gt.gmin (idx3 - (if b.1 then pow3 p1 else 2 * pow3 p1)
      - (if b.2 then pow3 p2 else 2 * pow3 p2)) with hgs
  have hfmin0' : (0 : ℝ) ≤ fx fminLo := fx_nonneg_of hfmin0
  have hfmax0' : (0 : ℝ) ≤ fx fmaxHi := fx_nonneg_of hfmax0
  have hV0 : (0 : ℝ) ≤ fx val := fx_nonneg_of hval0
  have hg0' : (0 : ℝ) ≤ gmin := by exact_mod_cast hg0
  have hqc0 : ∀ b, 0 ≤ qc b := by
    intro b
    simp only [hqc]
    split_ifs
    · have := mul_nonneg (hqa0 b.1) (hqb0 b.2)
      unfold shrD; rw [Int.shiftRight_eq_div_pow]; exact Int.ediv_nonneg this (by positivity)
    · exact le_max_right _ _
  -- the event volumes
  have hvol : ∀ b ∈ (Finset.univ : Finset (Bool × Bool)),
      ENNReal.ofReal (fx (qc b) * (volume Box).toReal) ≤
        volume (edgeEv k lo hi i1 j1 b.1 ∩ edgeEv k lo hi i2 j2 b.2) := by
    intro b _
    have h1 := probEv hPS hv (i := i1) (j := j1) (Fin.lt_def.mpr hij1) b.1
    have h2 := probEv hPS hv (i := i2) (j := j2) (Fin.lt_def.mpr hij2) b.2
    have h1' : ENNReal.ofReal (fx (qa b.1) * (volume Box).toReal) ≤ volume (edgeEv k lo hi i1 j1 b.1) := by
      convert h1 using 3; simp only [hqa]; split_ifs <;> rfl
    have h2' : ENNReal.ofReal (fx (qb b.2) * (volume Box).toReal) ≤ volume (edgeEv k lo hi i2 j2 b.2) := by
      convert h2 using 3; simp only [hqb]; split_ifs <;> rfl
    by_cases hd : dj
    · have hqcb : qc b = shrD (qa b.1 * qb b.2) PR := by simp only [hqc, if_pos hd]
      rw [hqcb]
      obtain ⟨d1, d2, d3, d4⟩ := hd
      have n1 : i1 ≠ i2 := fun h => by rw [bne_iff_ne] at d1; exact d1 (congrArg Fin.val h)
      have n2 : i1 ≠ j2 := fun h => by rw [bne_iff_ne] at d2; exact d2 (congrArg Fin.val h)
      have n3 : j1 ≠ i2 := fun h => by rw [bne_iff_ne] at d3; exact d3 (congrArg Fin.val h)
      have n4 : j1 ≠ j2 := fun h => by rw [bne_iff_ne] at d4; exact d4 (congrArg Fin.val h)
      have hind := hEI k lo hi hv i1 j1 i2 j2 n1 n2 n3 n4 _ _ (measurableSet_S b.1) (measurableSet_S b.2)
      rw [edgeEv_eq_sep, edgeEv_eq_sep] at hind
      have hsep : {x ∈ Box | sqDist (xcfg k x i1) (xcfg k x j1) ∈ (if b.1 then Iic (1 : ℝ) else Ioi 1) ∧
          sqDist (xcfg k x i2) (xcfg k x j2) ∈ (if b.2 then Iic (1 : ℝ) else Ioi 1)} =
          edgeEv k lo hi i1 j1 b.1 ∩ edgeEv k lo hi i2 j2 b.2 := by
        rw [← edgeEv_eq_sep lo hi i1 j1 b.1, ← edgeEv_eq_sep lo hi i2 j2 b.2]
        ext x; simp only [mem_setOf_eq, mem_inter_iff]; tauto
      rw [hsep] at hind
      have hI := indep_ofReal (fx_nonneg_of (hqa0 b.1)) (fx_nonneg_of (hqb0 b.2)) hQt
        (edgeEv_sub lo hi i1 j1 b.1) (edgeEv_sub lo hi i2 j2 b.2) hind h1' h2'
      refine le_trans (ENNReal.ofReal_le_ofReal ?_) hI
      exact mul_le_mul_of_nonneg_right (fx_shrD_le _ _) ENNReal.toReal_nonneg
    · have hqcb : qc b = max (qa b.1 + qb b.2 - ONE) 0 := by simp only [hqc, if_neg hd]
      rw [hqcb]
      have hF := frechet_ofReal (edgeEv_sub lo hi i1 j1 b.1) (edgeEv_sub lo hi i2 j2 b.2)
        (edgeEv_meas lo hi i2 j2 b.2) hQt h1' h2'
      have e : fx (max (qa b.1 + qb b.2 - ONE) 0) = max (fx (qa b.1) + fx (qb b.2) - 1) 0 := by
        rw [fx_max'', fx_sub'', fx_add'', fx_ONE', fx_zero']
      rw [e]; exact hF
  -- the core
  have hcore := core hEv hPB hQm hQt hfmin0' hfmax0' hV0 hg0' hfl hfu hint (Finset.univ : Finset (Bool × Bool))
    (fun b => edgeEv k lo hi i1 j1 b.1 ∩ edgeEv k lo hi i2 j2 b.2)
    (fun b => max ((gs b - gmin : ℤ) : ℝ) 0) (fun b => fx (qc b))
    (fun b _ => (edgeEv_meas lo hi i1 j1 b.1).inter (edgeEv_meas lo hi i2 j2 b.2))
    (fun b _ => inter_subset_left.trans (edgeEv_sub lo hi i1 j1 b.1))
    (fun b _ => le_max_right _ _) (fun b _ => fx_nonneg_of (hqc0 b)) hvol
    (fun x => 2 * dcG (unitGraph (xcfg k x)))
    (by
      intro x hx
      have hgm := gmin_le_two_g hk3 hgt hx
      set c1 := decide (sqDist (xcfg k x i1) (xcfg k x j1) ≤ 1) with hc1
      set c2 := decide (sqDist (xcfg k x i2) (xcfg k x j2) ≤ 1) with hc2
      have hgs := g_ge_set2 hk3 hgt hx hp1 hp2 hne h21 h22 c1 c2 hc1.symm hc2.symm
      have hind : ∀ b : Bool × Bool, (edgeEv k lo hi i1 j1 b.1 ∩ edgeEv k lo hi i2 j2 b.2).indicator
          (fun _ => (1 : ℝ)) x = if b = (c1, c2) then 1 else 0 := by
        intro b
        by_cases hb : b = (c1, c2)
        · rw [if_pos hb, Set.indicator_of_mem]
          rw [mem_inter_edgeEv hx, hb]; exact ⟨rfl, rfl⟩
        · rw [if_neg hb, Set.indicator_of_notMem]
          rw [mem_inter_edgeEv hx]
          rintro ⟨h1, h2⟩
          exact hb (Prod.ext h1.symm h2.symm)
      simp only [hind, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      have : ((gs (c1, c2) : ℤ) : ℝ) ≤ 2 * dcG (unitGraph (xcfg k x)) := hgs
      rcases le_total ((gs (c1, c2) - gmin : ℤ) : ℝ) 0 with hc | hc
      · rw [max_eq_right hc]; linarith
      · rw [max_eq_left hc]; push_cast at hc ⊢; linarith)
  refine le_trans (ENNReal.ofReal_le_ofReal ?_) hcore
  apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
  apply add_le_add le_rfl
  -- the code's score as a sum of four terms
  unfold scPair
  rw [foldl_ite_sum]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, zero_add, add_zero]
  rw [Fintype.sum_prod_type, Fintype.sum_bool, Fintype.sum_bool, Fintype.sum_bool]
  simp only [hgs, hqc, hqa, hqb, beq_self_eq_true, ite_true, Nat.zero_ne_one, beq_iff_eq, ite_false,
    Bool.false_eq_true]
  rw [fx_add'', fx_add'', fx_add'']
  conv_rhs => rw [add_assoc]
  refine add_le_add ?_ (add_le_add ?_ (add_le_add ?_ ?_)) <;>
    exact fx_score_le' _ _ _ (fx_evLB_le _ _ _ _) (EV_nonneg _ _ _ _)


/-! ## the branch -/

theorem extraSpec_of {k : ℕ} (hk3 : 3 ≤ k) {gt : GTab} (hgt : GTabSound k gt) (hEv : EventBoundProp)
    (hPB : PartitionBoundProp) (hPS : ProbStripsProp) (hEI : EdgeIndepProp) : ExtraSpec k gt := by
  intro lo hi hv f fminLo fmaxHi val hfmin0 hfmax0 hval0 hfl hfu hint hg0
  dsimp only
  -- the score 0 (interior term only)
  have h0 : ENNReal.ofReal ((volume (boxOf lo hi : Set (Fin (mDim k) → ℝ))).toReal *
      ((gt.gmin (val3 (stCode k lo hi)) : ℝ) * fx val + fx 0)) ≤
      ∫⁻ x in boxOf lo hi, ENNReal.ofReal (2 * dcG (unitGraph (xcfg k x))) * f x := by
    have hc := core hEv hPB (measurableSet_boxOf' lo hi) (volume_boxOf_ne_top' lo hi) (fx_nonneg_of hfmin0)
      (fx_nonneg_of hfmax0) (fx_nonneg_of hval0) (by exact_mod_cast hg0 : (0 : ℝ) ≤ gt.gmin (val3 (stCode k lo hi)))
      hfl hfu hint (∅ : Finset Bool) (fun _ => ∅) (fun _ => 0) (fun _ => 0)
      (fun b hb => absurd hb (Finset.notMem_empty b)) (fun b hb => absurd hb (Finset.notMem_empty b))
      (fun b hb => absurd hb (Finset.notMem_empty b)) (fun b hb => absurd hb (Finset.notMem_empty b))
      (fun b hb => absurd hb (Finset.notMem_empty b))
      (fun x => 2 * dcG (unitGraph (xcfg k x)))
      (fun x hx => by simpa using gmin_le_two_g hk3 hgt hx)
    simpa [fx_zero'] using hc
  have hS : ENNReal.ofReal ((volume (boxOf lo hi : Set (Fin (mDim k) → ℝ))).toReal *
      ((gt.gmin (val3 (stCode k lo hi)) : ℝ) * fx val +
        fx (singleLB gt (val3 (stCode k lo hi)) (gt.gmin (val3 (stCode k lo hi)))
          (probsOf (ptBoxes k lo hi) (pairList k) (stCode k lo hi)) fminLo fmaxHi val))) ≤
      ∫⁻ x in boxOf lo hi, ENNReal.ofReal (2 * dcG (unitGraph (xcfg k x))) * f x := by
    rw [singleLB_eq]
    rcases foldl_max_cases (scSingle gt (val3 (stCode k lo hi)) (gt.gmin (val3 (stCode k lo hi))) fminLo fmaxHi val)
      (probsOf (ptBoxes k lo hi) (pairList k) (stCode k lo hi)) 0 with h | ⟨e, he, h⟩
    · rw [h]; exact h0
    · rw [h]
      exact single_le hk3 hgt hEv hPB hPS hv hfmin0 hfmax0 hval0 hfl hfu hint hg0 he
  have hP : ENNReal.ofReal ((volume (boxOf lo hi : Set (Fin (mDim k) → ℝ))).toReal *
      ((gt.gmin (val3 (stCode k lo hi)) : ℝ) * fx val +
        fx (pairsLB gt (val3 (stCode k lo hi)) (gt.gmin (val3 (stCode k lo hi)))
          (probsOf (ptBoxes k lo hi) (pairList k) (stCode k lo hi)) fminLo fmaxHi val))) ≤
      ∫⁻ x in boxOf lo hi, ENNReal.ofReal (2 * dcG (unitGraph (xcfg k x))) * f x := by
    rw [pairsLB_eq]
    rcases foldl_pairs_cases (probsOf (ptBoxes k lo hi) (pairList k) (stCode k lo hi)) (fun e1 e2 => e1.1 < e2.1)
      (scPair gt (val3 (stCode k lo hi)) (gt.gmin (val3 (stCode k lo hi))) fminLo fmaxHi val)
      (probsOf (ptBoxes k lo hi) (pairList k) (stCode k lo hi)) 0 (fun e he => he) with
      h | ⟨e1, he1, e2, he2, hlt, h⟩
    · rw [h]; exact h0
    · rw [h]
      exact pair_le hk3 hgt hEv hPB hPS hEI hv hfmin0 hfmax0 hval0 hfl hfu hint hg0 he1 he2 hlt
  rcases le_total (singleLB gt (val3 (stCode k lo hi)) (gt.gmin (val3 (stCode k lo hi)))
      (probsOf (ptBoxes k lo hi) (pairList k) (stCode k lo hi)) fminLo fmaxHi val)
    (pairsLB gt (val3 (stCode k lo hi)) (gt.gmin (val3 (stCode k lo hi)))
      (probsOf (ptBoxes k lo hi) (pairList k) (stCode k lo hi)) fminLo fmaxHi val) with hle | hle
  · rw [max_eq_right hle]; exact hP
  · rw [max_eq_left hle]; exact hS


end DX

end BHH
