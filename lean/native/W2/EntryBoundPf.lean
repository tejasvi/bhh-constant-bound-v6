/-
`EntryBound` (`W2/TSProps.lean`) from the soundness of the two paths of `entryF` (fallback and vertex path) and the
nondegeneracy check `nondegOK`.
-/
import W2.EntrySound

open MeasureTheory Set Real
open scoped ENNReal

noncomputable section

namespace BHH.W2

open W2C BHH.Cert BHH

theorem entryF_eq (prune : Bool) (rings : Array Ring) (ad : AData) (dd : DData) (ir ir2 : ℕ) :
    entryF prune rings ad dd ir ir2 = entryG prune rings ad dd ir ir2 := rfl

set_option maxHeartbeats 1000000 in
/-- One entry: the integral of `A_2` over the canonical pair is at most the computed `ā` times the areas. -/
theorem entry_sound (hV : VertexLemmaSeg) (hG : GreenFormula) (hRS : RingSound) (hAS : AngleSound)
    (hAR : AngleRange) (hFS : FrangeSound) (hDS : DistSound) (hA1 : A1Radial) (hA2 : A2Union) (hA2le : A2LeA1)
    (hPM : PairMean) (hSC : SectorCen)
    {g : Grid} (hN1 : 0 < g.N1) (hN2 : 0 < g.N2) (hNT : 2 ≤ g.NT) (hNT30 : g.NT ≤ 2 ^ 30) (hNS : 0 < g.NSUB)
    {ir ir2 : ℕ} (hir : ir < g.NR) (hir2 : ir2 < g.NR) {d : ℤ} (hd : |d| < g.NT)
    (hr1 : ringOK g ir = true) (hr2 : ringOK g ir2 = true)
    (hok : entryOK g.prune ((Array.range g.NR).map (mkRing g)) (mkAData g) (mkDData g d) ir ir2 = true) :
    ∫ p in sector ((gR g).rad ir) ((gR g).rad (ir + 1)) 0 (π / g.NT) ×ˢ
        sector ((gR g).rad ir2) ((gR g).rad (ir2 + 1)) (d * (π / g.NT)) ((d + 1) * (π / g.NT)), A2 p.1 p.2 ≤
      fx (entryF g.prune ((Array.range g.NR).map (mkRing g)) (mkAData g) (mkDData g d) ir ir2).2 *
        (volume (sector ((gR g).rad ir) ((gR g).rad (ir + 1)) 0 (π / g.NT))).toReal *
        (volume (sector ((gR g).rad ir2) ((gR g).rad (ir2 + 1)) (d * (π / g.NT)) ((d + 1) * (π / g.NT)))).toReal := by
  have hR1 : ((Array.range g.NR).map (mkRing g))[ir]! = mkRing g ir := rings_getElem g hir
  have hR2 : ((Array.range g.NR).map (mkRing g))[ir2]! = mkRing g ir2 := rings_getElem g hir2
  have hZ := secOK_z g hN1 hN2 hNT ir
  have hZ' := secOK_z' g hN1 hN2 hNT ir2 hd
  have hrok : 0 < (Iv.sub (Iv.sqr (radIv g (ir2 + 1))) (Iv.sqr (radIv g ir2))).lo ∧
      0 < (Iv.div2e (dthIv g) 1).lo := by
    simp only [ringOK, Bool.and_eq_true, decide_eq_true_eq] at hr2; exact hr2
  obtain ⟨-, -, -, -, -, -, hhi, -⟩ := hRS g hN1 hN2 hNT hNS ir2 hir2 hrok.1 hrok.2
  have hvZ := volume_sector_pos hZ
  have hvZ' := volume_sector_pos hZ'
  have hfb : ∫ p in sector ((gR g).rad ir) ((gR g).rad (ir + 1)) 0 (π / g.NT) ×ˢ
        sector ((gR g).rad ir2) ((gR g).rad (ir2 + 1)) (d * (π / g.NT)) ((d + 1) * (π / g.NT)), A2 p.1 p.2 ≤
      fx (mkRing g ir2).euHi *
        (volume (sector ((gR g).rad ir) ((gR g).rad (ir + 1)) 0 (π / g.NT))).toReal *
        (volume (sector ((gR g).rad ir2) ((gR g).rad (ir2 + 1)) (d * (π / g.NT)) ((d + 1) * (π / g.NT)))).toReal := by
    refine (fallback_bound hG hA1 hA2le hZ hZ').trans ?_
    have := mul_pos hvZ hvZ'
    nlinarith
  rw [entryF_eq]
  unfold entryG
  dsimp only
  split
  · rw [hR2]; exact hfb
  · next ur hur =>
    split
    · rw [hR2]; exact hfb
    · next er her =>
      have hv := entry_vertex hV hG hRS hAS hAR hFS hDS hA1 hA2 hPM hSC hN1 hN2 hNT hNT30 hNS hir hir2 hd hr1 hr2
        hok hur her
      rw [hR2, hR1, fx_min]
      have hV : 0 ≤ (volume (sector ((gR g).rad ir) ((gR g).rad (ir + 1)) 0 (π / g.NT))).toReal *
          (volume (sector ((gR g).rad ir2) ((gR g).rad (ir2 + 1)) (d * (π / g.NT))
            ((d + 1) * (π / g.NT)))).toReal := (mul_pos hvZ hvZ').le
      rw [mul_assoc, min_mul_of_nonneg _ _ hV]
      rw [mul_assoc] at hfb hv
      exact le_min hfb hv

lemma mkDTab_getElem (g : Grid) {d : ℤ} (hd : |d| < g.NT) :
    (mkDTab g)[(d + ((g.NT - 1 : ℕ) : ℤ)).toNat]! = mkDData g d := by
  have hND : g.ND = 2 * g.NT - 1 := rfl
  have hlt : (d + ((g.NT - 1 : ℕ) : ℤ)).toNat < g.ND := by rw [abs_lt] at hd; rw [hND]; omega
  unfold mkDTab
  rw [getElem!_map _ _ (by simpa using hlt), range_getElem! hlt]
  congr 1
  rw [abs_lt] at hd
  simp only [Int.ofNat_eq_coe]
  omega

/-- The nondegeneracy check gives `ringOK` for all rings and `entryOK` for all entries. -/
theorem nondeg_spec {g : Grid} (h : nondegOK g = true) :
    (∀ j, j < g.NR → ringOK g j = true) ∧
    ∀ ir ir2 : ℕ, ir < g.NR → ir2 < g.NR → ∀ d : ℤ, |d| < g.NT →
      entryOK g.prune ((Array.range g.NR).map (mkRing g)) (mkAData g) (mkDData g d) ir ir2 = true := by
  unfold nondegOK at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, List.all_map] at h
  obtain ⟨hr, he⟩ := h
  refine ⟨hr, fun ir ir2 hir hir2 d hd => ?_⟩
  have h1 := he ir hir
  simp only [Function.comp, task_get_spawn, List.all_eq_true, List.mem_range] at h1
  have hND : g.ND = 2 * g.NT - 1 := rfl
  have hdi : (d + ((g.NT - 1 : ℕ) : ℤ)).toNat < g.ND := by rw [abs_lt] at hd; rw [hND]; omega
  have hq : ir2 * g.ND + (d + ((g.NT - 1 : ℕ) : ℤ)).toNat < g.NR * g.ND := by nlinarith
  have := h1 _ hq
  rw [flat_mod _ _ hdi, flat_div _ _ hdi, mkDTab_getElem g hd] at this
  exact this

/-- **EntryBound** for any grid passing the nondegeneracy check. -/
theorem entryBound_of (hV : VertexLemmaSeg) (hG : GreenFormula) (hRS : RingSound) (hAS : AngleSound)
    (hAR : AngleRange) (hFS : FrangeSound) (hDS : DistSound) (hA1 : A1Radial) (hA2 : A2Union) (hA2le : A2LeA1)
    (hPM : PairMean) (hSC : SectorCen)
    {g : Grid} (hN1 : 0 < g.N1) (hN2 : 0 < g.N2) (hNT : 2 ≤ g.NT) (hNT30 : g.NT ≤ 2 ^ 30) (hNS : 0 < g.NSUB)
    (hnd : nondegOK g = true) : EntryBound g := by
  obtain ⟨hr, he⟩ := nondeg_spec hnd
  intro ir ir2 hir hir2 d hd
  exact entry_sound hV hG hRS hAS hAR hFS hDS hA1 hA2 hA2le hPM hSC hN1 hN2 hNT hNT30 hNS hir hir2 hd
    (hr ir hir) (hr ir2 hir2) (he ir ir2 hir hir2 d hd)

end BHH.W2
