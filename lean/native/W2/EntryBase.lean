/-
Basic facts for the entry soundness: ring data of the run, the canonical cells are admissible sectors, integrability
on products of sectors, and the fallback bound `∫∫ A_2 ≤ meanA1(z-ring) |Z| |Z'|`.
-/
import W2.EntryGeo
import W2.TSProps
import W2.DiscCells

open MeasureTheory Set Real
open scoped ENNReal

noncomputable section

namespace BHH.W2

open W2C BHH.Cert BHH

lemma rings_getElem (g : Grid) {j : ℕ} (hj : j < g.NR) : ((Array.range g.NR).map (mkRing g))[j]! = mkRing g j := by
  rw [getElem!_map _ _ (by simpa using hj), range_getElem! hj]

lemma rad_lt (g : GridR) (h1 : 0 < g.N1) (h2 : 0 < g.N2) (j : ℕ) : g.rad j < g.rad (j + 1) := by
  unfold GridR.rad
  have h1' : (0 : ℝ) < g.N1 := by exact_mod_cast h1
  have h2' : (0 : ℝ) < g.N2 := by exact_mod_cast h2
  by_cases hj : j + 1 ≤ g.N1
  · rw [if_pos (by omega), if_pos hj]
    push_cast
    exact div_lt_div_of_pos_right (by linarith) h1'
  · rw [if_neg hj]
    by_cases hj' : j ≤ g.N1
    · have hjN : j = g.N1 := by omega
      rw [hjN, if_pos le_rfl, div_self h1'.ne']
      have : ((g.N1 + 1 - g.N1 : ℕ) : ℝ) = 1 := by simp
      rw [this]; linarith [div_pos one_pos h2']
    · rw [if_neg hj']
      have e : (j + 1 - g.N1 : ℕ) = (j - g.N1 : ℕ) + 1 := by omega
      rw [e]; push_cast
      linarith [div_lt_div_of_pos_right (lt_add_one ((j - g.N1 : ℕ) : ℝ)) h2']

/-- The canonical z-cell `(0, h)` of ring `j` is an admissible sector. -/
lemma secOK_z (g : Grid) (h1 : 0 < g.N1) (h2 : 0 < g.N2) (hNT : 2 ≤ g.NT) (j : ℕ) :
    SecOK ((gR g).rad j) ((gR g).rad (j + 1)) 0 (π / g.NT) := by
  have hN : (2 : ℝ) ≤ g.NT := by exact_mod_cast hNT
  have hNp : (0 : ℝ) < g.NT := by linarith
  refine ⟨GridR.rad_nonneg (gR g) j, rad_lt (gR g) h1 h2 j, by linarith [Real.pi_pos], div_pos Real.pi_pos hNp,
    ?_, ?_⟩
  · rw [div_le_iff₀ hNp]; nlinarith [Real.pi_pos]
  · rw [sub_zero, div_le_div_iff₀ hNp (by norm_num)]; nlinarith [Real.pi_pos]

/-- The canonical z'-cell `(d h, (d+1) h)` of ring `j` (`|d| < NT`) is an admissible sector. -/
lemma secOK_z' (g : Grid) (h1 : 0 < g.N1) (h2 : 0 < g.N2) (hNT : 2 ≤ g.NT) (j : ℕ) {d : ℤ} (hd : |d| < g.NT) :
    SecOK ((gR g).rad j) ((gR g).rad (j + 1)) (d * (π / g.NT)) ((d + 1) * (π / g.NT)) := by
  have hN : (2 : ℝ) ≤ g.NT := by exact_mod_cast hNT
  have hNp : (0 : ℝ) < g.NT := by linarith
  have hh : 0 < π / g.NT := div_pos Real.pi_pos hNp
  have hd1 : (-(g.NT : ℤ) + 1 : ℤ) ≤ d := by rw [abs_lt] at hd; omega
  have hd2 : d + 1 ≤ (g.NT : ℤ) := by rw [abs_lt] at hd; omega
  have hd1' : (-(g.NT : ℝ) + 1) ≤ d := by exact_mod_cast hd1
  have hd2' : (d : ℝ) + 1 ≤ g.NT := by exact_mod_cast hd2
  have hNh : (g.NT : ℝ) * (π / g.NT) = π := by field_simp
  refine ⟨GridR.rad_nonneg (gR g) j, rad_lt (gR g) h1 h2 j, ?_, ?_, ?_, ?_⟩
  · nlinarith
  · nlinarith
  · nlinarith
  · have : (d + 1 : ℝ) * (π / g.NT) - d * (π / g.NT) = π / g.NT := by ring
    rw [this, div_le_div_iff₀ hNp (by norm_num)]; nlinarith [Real.pi_pos]

/-! ## Integrability on products of sectors -/

lemma volume_prod_ne_top {S S' : Set Pt} (h : volume S ≠ ⊤) (h' : volume S' ≠ ⊤) : volume (S ×ˢ S') ≠ ⊤ := by
  rw [Measure.volume_eq_prod, Measure.prod_prod]
  exact ENNReal.mul_ne_top h h'

lemma integrableOn_bdd {s : Set (Pt × Pt)} (hs : volume s ≠ ⊤) {f : Pt × Pt → ℝ} (hf : Measurable f) {M : ℝ}
    (hb : ∀ p, |f p| ≤ M) : IntegrableOn f s :=
  Measure.integrableOn_of_bounded (M := M) hs hf.aestronglyMeasurable
    (Filter.Eventually.of_forall fun p => by rw [Real.norm_eq_abs]; exact hb p)

lemma integrableOn_A2 {S S' : Set Pt} (h : volume S ≠ ⊤) (h' : volume S' ≠ ⊤) :
    IntegrableOn (fun p : Pt × Pt => A2 p.1 p.2) (S ×ˢ S') :=
  integrableOn_bdd (volume_prod_ne_top h h') measurable_A2 (M := π) fun p => by
    rw [abs_of_nonneg (A2_nonneg _ _)]; exact A2_le_pi _ _

lemma integrableOn_A1_snd {S S' : Set Pt} (h : volume S ≠ ⊤) (h' : volume S' ≠ ⊤) :
    IntegrableOn (fun p : Pt × Pt => A1 p.2) (S ×ˢ S') :=
  integrableOn_bdd (volume_prod_ne_top h h') (measurable_A1.comp measurable_snd) (M := π) fun p => by
    rw [abs_of_nonneg (A1_nonneg _)]; exact A1_le_pi _

lemma integrableOn_A1_fst {S S' : Set Pt} (h : volume S ≠ ⊤) (h' : volume S' ≠ ⊤) :
    IntegrableOn (fun p : Pt × Pt => A1 p.1) (S ×ˢ S') :=
  integrableOn_bdd (volume_prod_ne_top h h') (measurable_A1.comp measurable_fst) (M := π) fun p => by
    rw [abs_of_nonneg (A1_nonneg _)]; exact A1_le_pi _

lemma sector_ne_top {r1 r2 a b : ℝ} (h : SecOK r1 r2 a b) : volume (sector r1 r2 a b) ≠ ⊤ := by
  rw [sectorArea r1 r2 a b h]; exact ENNReal.ofReal_ne_top

lemma sector_ne_zero {r1 r2 a b : ℝ} (h : SecOK r1 r2 a b) : volume (sector r1 r2 a b) ≠ 0 := by
  intro h0
  have := volume_sector_pos h
  rw [h0, ENNReal.toReal_zero] at this
  exact lt_irrefl 0 this

lemma measurableSet_sector {r1 r2 a b : ℝ} (h : SecOK r1 r2 a b) : MeasurableSet (sector r1 r2 a b) := by
  rw [sector_eq_pcell]
  exact measurableSet_pcell h.1 h.2.2.1 h.2.2.2.2.1

/-! ## The fallback bound -/

/-- `∫_{Z×Z'} A_2 ≤ meanA1(q1, q2) |Z| |Z'|` (`A_2(w, z) ≤ A_1(z)`). -/
theorem fallback_bound (hG : GreenFormula) (hA1 : A1Radial) (hA2le : A2LeA1) {r1 r2 a b q1 q2 a' b' : ℝ}
    (hZ : SecOK r1 r2 a b) (hZ' : SecOK q1 q2 a' b') :
    ∫ p in sector r1 r2 a b ×ˢ sector q1 q2 a' b', A2 p.1 p.2 ≤
      meanA1 q1 q2 * (volume (sector r1 r2 a b)).toReal * (volume (sector q1 q2 a' b')).toReal := by
  have h1 : ∫ p in sector r1 r2 a b ×ˢ sector q1 q2 a' b', A2 p.1 p.2 ≤
      ∫ p in sector r1 r2 a b ×ˢ sector q1 q2 a' b', A1 p.2 :=
    setIntegral_mono (integrableOn_A2 (sector_ne_top hZ) (sector_ne_top hZ'))
      (integrableOn_A1_snd (sector_ne_top hZ) (sector_ne_top hZ')) fun p => hA2le p.1 p.2
  rw [setIntegral_snd', integral_A1_sector hG hA1 hZ'] at h1
  linarith

end BHH.W2
