/-
Soundness of one table entry (`W2C.entryF`): the integral of `A_2` over the canonical cell pair is at most the
computed `ā` times the two areas (`EntryBound`), from the vertex lemma integrated over the pair (T6) and the
interval soundness of the per-ring data, the angle data, Lemma 4 and the distance bounds (T1-T4), with the
fallback `A_2 ≤ A_1(z)` (T5).
-/
import W2.EntryFold
import BHH.UnionSound

open MeasureTheory Set Real
open scoped ENNReal

noncomputable section

namespace BHH.W2

open W2C BHH.Cert BHH

/-! ## The real data of the pairs -/

/-- the pair index of `(i, j)`: `0` for `(0, 1)`, `1` for `(1, 2)`, `2` otherwise (`(0, 2)`) -/
def pIdx (i j : Fin 3) : ℕ := if i.val = 0 ∧ j.val = 1 then 0 else if i.val = 1 ∧ j.val = 2 then 1 else 2

def dloOf (C : ECore) (i j : Fin 3) : ℝ := fx (C.dmn.getD (pIdx i j) 0)
def dhiOf (C : ECore) (i j : Fin 3) : ℝ := fx (C.dmx.getD (pIdx i j) 0)
def firstOf (C : ECore) (i j : Fin 3) : Bool :=
  decide (C.dmn.getD (pIdx i j) 0 < 2 * ONE) && decide (useFirstOf (C.dmx.getD (pIdx i j) 0))
def epsOf (C : ECore) (i : Fin 3) : ℝ := fx (C.epsR.getD i.val 0)

lemma secRho_shift (r1 r2 a h : ℝ) : secRho r1 r2 a (a + h) = secRho r1 r2 0 h := by
  unfold secRho; congr 3 <;> ring

lemma fx_neg' (a : ℤ) : fx (-a) = -fx a := by unfold fx; push_cast; ring

lemma ptsCfg_C0 (C : ECore) (hC : C.pts = [(C.p0x, C.p0y), (0, 0), (C.p2x, C.p2y)]) :
    ptsCfg 3 C.pts 0 = (fx C.p0x, fx C.p0y) := by
  simp [ptsCfg, hC]

lemma ptsCfg_C1 (C : ECore) (hC : C.pts = [(C.p0x, C.p0y), (0, 0), (C.p2x, C.p2y)]) :
    ptsCfg 3 C.pts 1 = 0 := by
  simp [ptsCfg, hC, fx]

lemma ptsCfg_C2 (C : ECore) (hC : C.pts = [(C.p0x, C.p0y), (0, 0), (C.p2x, C.p2y)]) :
    ptsCfg 3 C.pts 2 = (fx C.p2x, fx C.p2y) := by
  simp [ptsCfg, hC]

lemma sqrt_hi_nonneg (a : Iv) : 0 ≤ (Iv.sqrt a).hi := by
  unfold Iv.sqrt; dsimp only; split_ifs <;> positivity

lemma distHi_nonneg (px py : Iv) (qx qy : ℤ) : 0 ≤ distHi px py qx qy := sqrt_hi_nonneg _

lemma epsCell_nonneg (R : Ring) (ch : Iv) : 0 ≤ epsCell R ch := by
  unfold epsCell; dsimp only; linarith [sqrt_hi_nonneg ⟨Max.max (Max.max
    (Iv.add (Iv.sqr R.r1) (Iv.sub (Iv.sqr R.rhoc) (Iv.mul2e (Iv.mul (Iv.mul R.r1 R.rhoc) ch) 1))).hi
    (Iv.add (Iv.sqr R.r2) (Iv.sub (Iv.sqr R.rhoc) (Iv.mul2e (Iv.mul (Iv.mul R.r2 R.rhoc) ch) 1))).hi) 0,
    Max.max (Max.max
    (Iv.add (Iv.sqr R.r1) (Iv.sub (Iv.sqr R.rhoc) (Iv.mul2e (Iv.mul (Iv.mul R.r1 R.rhoc) ch) 1))).hi
    (Iv.add (Iv.sqr R.r2) (Iv.sub (Iv.sqr R.rhoc) (Iv.mul2e (Iv.mul (Iv.mul R.r2 R.rhoc) ch) 1))).hi) 0⟩]

lemma momHi_nonneg (g : Grid) (j : ℕ) : 0 ≤ (mkRing g j).momHi := le_max_right _ _

lemma sector_bounded {r1 r2 a b : ℝ} (h0 : 0 ≤ r1) : Bornology.IsBounded (sector r1 r2 a b) := by
  rw [Metric.isBounded_iff_subset_closedBall (0 : Pt)]
  refine ⟨max r2 0, fun z hz => ?_⟩
  obtain ⟨p, hp, rfl⟩ := hz
  simp only [mem_prod, mem_Ioo] at hp
  simp only [Metric.mem_closedBall, dist_zero_right, polarCoord_symm_apply, Prod.norm_def, Real.norm_eq_abs]
  have hρ : 0 ≤ p.1 := by linarith [hp.1.1]
  have h1 : |p.1 * Real.cos p.2| ≤ max r2 0 := by
    rw [abs_mul, abs_of_nonneg hρ]
    calc p.1 * |Real.cos p.2| ≤ p.1 * 1 := mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) hρ
      _ ≤ max r2 0 := by linarith [hp.1.2, le_max_left r2 0]
  have h2 : |p.1 * Real.sin p.2| ≤ max r2 0 := by
    rw [abs_mul, abs_of_nonneg hρ]
    calc p.1 * |Real.sin p.2| ≤ p.1 * 1 := mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _) hρ
      _ ≤ max r2 0 := by linarith [hp.1.2, le_max_left r2 0]
  exact max_le h1 h2

lemma fx_finset_sum (s : Finset ℕ) (f : ℕ → ℤ) : fx (∑ p ∈ s, f p) = ∑ p ∈ s, fx (f p) := by
  unfold fx; push_cast; rw [Finset.sum_div]

/-- The nondegeneracy tests of a pair on the path taken. -/
lemma pairOK_spec {prune : Bool} {C : ECore} {p : ℕ} (h : pairOK prune C p = true)
    (hdn1 : ¬ 2 * ONE ≤ C.dmn.getD p 0) (hdn2 : 0 < C.dmn.getD p 0) {i j l : ℕ} (hijl : pairIJL p = (i, j, l)) :
    (useFirstOf (C.dmx.getD p 0) →
      0 < (Iv.sqrt (Iv.sub (Iv.int 4) (Iv.sqr ⟨C.dmx.getD p 0, C.dmx.getD p 0⟩))).lo) ∧
    (prune = true → ∀ ax ay bx by_ : ℤ, C.pts.getD i (0, 0) = (ax, ay) → C.pts.getD j (0, 0) = (bx, by_) →
      0 < (bx - ax) * (bx - ax) + (by_ - ay) * (by_ - ay) →
      (bx - ax) * (bx - ax) + (by_ - ay) * (by_ - ay) < 4 * ONE * ONE →
      0 < (Iv.sqrt (Iv.add (Iv.sqr (Iv.pt (bx - ax))) (Iv.sqr (Iv.pt (by_ - ay))))).lo) := by
  unfold pairOK at h
  rw [if_neg (by omega), Bool.and_eq_true] at h
  obtain ⟨hA, hB⟩ := h
  constructor
  · intro hf
    simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq] at hA
    exact hA.resolve_left (not_not.mpr hf)
  · intro hp ax ay bx by_ hA' hB' h1 h2
    subst hp
    rw [hijl] at hB
    simp only [hA', hB', Bool.not_true, Bool.false_or, Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
      decide_eq_true_eq] at hB
    exact hB.resolve_left (not_not.mpr ⟨h1, h2⟩)

/-! ## The vertex path of an entry -/

set_option maxHeartbeats 4000000 in
/-- The vertex path of `entryF`: if the union area at the expansion point and the remainder fold succeed, the integral
of `A_2` over the canonical pair is at most `lv = A(c)⁺ + 2 (e0 + e2) + er - (π⁻ + euLo) + 2ulp` times the areas. -/
theorem entry_vertex (hV : VertexLemmaSeg) (hG : GreenFormula) (hRS : RingSound) (hAS : AngleSound)
    (hAR : AngleRange) (hFS : FrangeSound) (hDS : DistSound) (hA1 : A1Radial) (hA2 : A2Union) (hPM : PairMean)
    (hSC : SectorCen)
    {g : Grid} (hN1 : 0 < g.N1) (hN2 : 0 < g.N2) (hNT : 2 ≤ g.NT) (hNT30 : g.NT ≤ 2 ^ 30) (hNS : 0 < g.NSUB)
    {ir ir2 : ℕ} (hir : ir < g.NR) (hir2 : ir2 < g.NR) {d : ℤ} (hd : |d| < g.NT)
    (hr1 : ringOK g ir = true) (hr2 : ringOK g ir2 = true)
    (hok : entryOK g.prune ((Array.range g.NR).map (mkRing g)) (mkAData g) (mkDData g d) ir ir2 = true)
    {ur : UnionRes}
    (hur : BHH.Cert.unionArea cosSin
      (mkECore ((Array.range g.NR).map (mkRing g)) (mkAData g) (mkDData g d) ir ir2).pts ONE unionCand = some ur)
    {er : ℤ}
    (her : [0, 1, 2].foldl
      (pairStep g.prune (mkECore ((Array.range g.NR).map (mkRing g)) (mkAData g) (mkDData g d) ir ir2)) (some 0) =
        some er) :
    ∫ p in sector ((gR g).rad ir) ((gR g).rad (ir + 1)) 0 (π / g.NT) ×ˢ
        sector ((gR g).rad ir2) ((gR g).rad (ir2 + 1)) (d * (π / g.NT)) ((d + 1) * (π / g.NT)), A2 p.1 p.2 ≤
      fx (ur.A.hi + 2 * ((mkECore ((Array.range g.NR).map (mkRing g)) (mkAData g) (mkDData g d) ir ir2).e0 +
          (mkECore ((Array.range g.NR).map (mkRing g)) (mkAData g) (mkDData g d) ir ir2).e2) + er -
          (piLo + (mkRing g ir).euLo) + 2) *
        (volume (sector ((gR g).rad ir) ((gR g).rad (ir + 1)) 0 (π / g.NT))).toReal *
        (volume (sector ((gR g).rad ir2) ((gR g).rad (ir2 + 1)) (d * (π / g.NT)) ((d + 1) * (π / g.NT)))).toReal := by
  set rings := (Array.range g.NR).map (mkRing g) with hrings
  set ad := mkAData g with had
  set dd := mkDData g d with hddd
  set C := mkECore rings ad dd ir ir2 with hC
  set h := π / (g.NT : ℝ) with hhdef
  set r1 := (gR g).rad ir with hr1def
  set r2 := (gR g).rad (ir + 1) with hr2def
  set q1 := (gR g).rad ir2 with hq1def
  set q2 := (gR g).rad (ir2 + 1) with hq2def
  have hR1 : rings[ir]! = mkRing g ir := rings_getElem g hir
  have hR2 : rings[ir2]! = mkRing g ir2 := rings_getElem g hir2
  -- ring facts (T1)
  have hrok : ∀ j, ringOK g j = true →
      0 < (Iv.sub (Iv.sqr (radIv g (j + 1))) (Iv.sqr (radIv g j))).lo ∧ 0 < (Iv.div2e (dthIv g) 1).lo := by
    intro j hj; simp only [ringOK, Bool.and_eq_true, decide_eq_true_eq] at hj; exact hj
  obtain ⟨a1, b1⟩ := hrok ir hr1
  obtain ⟨a2, b2⟩ := hrok ir2 hr2
  obtain ⟨m1r1, m1r2, -, m1rho, m1mom, m1lo, -, -⟩ := hRS g hN1 hN2 hNT hNS ir hir a1 b1
  obtain ⟨m2r1, m2r2, -, m2rho, m2mom, -, -, -⟩ := hRS g hN1 hN2 hNT hNS ir2 hir2 a2 b2
  -- angle facts (T2)
  obtain ⟨mch, msh, hddf⟩ := hAS g hNT hNT30
  obtain ⟨mcx, msy, mcmin, mcmax⟩ := hddf d hd
  -- the cells
  have hZ : SecOK r1 r2 0 h := secOK_z g hN1 hN2 hNT ir
  have hZ' : SecOK q1 q2 (d * h) ((d + 1) * h) := secOK_z' g hN1 hN2 hNT ir2 hd
  have hhpos : 0 < h := hZ.2.2.2.1
  have hNh : h * (g.NT : ℝ) = π := by rw [hhdef]; field_simp
  have hcosh : 0 ≤ Real.cos (h / 2) := by
    have := cos_half_nonneg hZ; rwa [sub_zero] at this
  -- centroids
  set CZ := secCentroid r1 r2 0 h with hCZ
  set CZ' := secCentroid q1 q2 (d * h) ((d + 1) * h) with hCZ'
  have hsh' : secRho q1 q2 (d * h) ((d + 1) * h) = secRho q1 q2 0 h := by
    rw [show (d + 1 : ℝ) * h = d * h + h by ring]; exact secRho_shift _ _ _ _
  have hCZ1 : ivMem CZ.1 (Iv.mul (mkRing g ir).rhoc ad.ch) := by
    show ivMem (secRho r1 r2 0 h * Real.cos ((0 + h) / 2)) _
    rw [zero_add]; exact Iv.mem_mul m1rho mch
  have hCZ2 : ivMem CZ.2 (Iv.mul (mkRing g ir).rhoc ad.sh) := by
    show ivMem (secRho r1 r2 0 h * Real.sin ((0 + h) / 2)) _
    rw [zero_add]; exact Iv.mem_mul m1rho msh
  have hCZ'1 : ivMem CZ'.1 (Iv.mul (mkRing g ir2).rhoc dd.cx) := by
    show ivMem (secRho q1 q2 (d * h) ((d + 1) * h) * Real.cos ((d * h + (d + 1) * h) / 2)) _
    rw [hsh', show (d * h + (d + 1) * h) / 2 = (2 * d + 1) * h / 2 by ring]; exact Iv.mem_mul m2rho mcx
  have hCZ'2 : ivMem CZ'.2 (Iv.mul (mkRing g ir2).rhoc dd.sy) := by
    show ivMem (secRho q1 q2 (d * h) ((d + 1) * h) * Real.sin ((d * h + (d + 1) * h) / 2)) _
    rw [hsh', show (d * h + (d + 1) * h) / 2 = (2 * d + 1) * h / 2 by ring]; exact Iv.mem_mul m2rho msy
  -- the code data
  have hCp0x : C.p0x = -(midPt (Iv.mul (mkRing g ir).rhoc ad.ch)) := by rw [← hR1]; rfl
  have hCp0y : C.p0y = -(midPt (Iv.mul (mkRing g ir).rhoc ad.sh)) := by rw [← hR1]; rfl
  have hCp2x : C.p2x = midPt (Iv.mul (mkRing g ir2).rhoc dd.cx) := by rw [← hR2]; rfl
  have hCp2y : C.p2y = midPt (Iv.mul (mkRing g ir2).rhoc dd.sy) := by rw [← hR2]; rfl
  have hCe0 : C.e0 = distHi (Iv.mul (mkRing g ir).rhoc ad.ch) (Iv.mul (mkRing g ir).rhoc ad.sh) (-C.p0x) (-C.p0y) := by
    rw [← hR1]; rfl
  have hCe2 : C.e2 = distHi (Iv.mul (mkRing g ir2).rhoc dd.cx) (Iv.mul (mkRing g ir2).rhoc dd.sy) C.p2x C.p2y := by
    rw [← hR2]; rfl
  have hCpts : C.pts = [(C.p0x, C.p0y), (0, 0), (C.p2x, C.p2y)] := rfl
  set c : Fin 3 → Pt := ptsCfg 3 C.pts with hcdef
  have hc0 : c 0 = (fx C.p0x, fx C.p0y) := ptsCfg_C0 C hCpts
  have hc1 : c 1 = 0 := ptsCfg_C1 C hCpts
  have hc2 : c 2 = (fx C.p2x, fx C.p2y) := ptsCfg_C2 C hCpts
  have hnc0 : -c 0 = (fx (-C.p0x), fx (-C.p0y)) := by rw [hc0, fx_neg', fx_neg', Prod.neg_mk]
  -- centroid distances
  have he0 : edist2 CZ (-c 0) ≤ fx C.e0 := by
    rw [hnc0, hCe0]; exact hDS.1 _ _ (-C.p0x) (-C.p0y) CZ.1 CZ.2 hCZ1 hCZ2
  have he2 : edist2 CZ' (c 2) ≤ fx C.e2 := by
    rw [hc2, hCe2]; exact hDS.1 _ _ C.p2x C.p2y CZ'.1 CZ'.2 hCZ'1 hCZ'2
  obtain ⟨hcenZ, hmomZ⟩ := hSC _ _ _ _ hZ
  obtain ⟨hcenZ', hmomZ'⟩ := hSC _ _ _ _ hZ'
  have hM0 : (volume (sector r1 r2 0 h)).toReal⁻¹ * ∫ w in sector r1 r2 0 h, sqDist w (cen (sector r1 r2 0 h)) ≤
      fx (mkRing g ir).momHi := by rw [hmomZ]; exact m1mom
  have hM2 : (volume (sector q1 q2 (d * h) ((d + 1) * h))).toReal⁻¹ *
      ∫ z in sector q1 q2 (d * h) ((d + 1) * h), sqDist z (cen (sector q1 q2 (d * h) ((d + 1) * h))) ≤
      fx (mkRing g ir2).momHi := by rw [hmomZ', hsh']; exact m2mom
  have hM0n : 0 ≤ fx (mkRing g ir).momHi := fx_nonneg_iff.mpr (momHi_nonneg g ir)
  have hM2n : 0 ≤ fx (mkRing g ir2).momHi := fx_nonneg_iff.mpr (momHi_nonneg g ir2)
  have he0n : 0 ≤ fx C.e0 := le_trans (edist2_nonneg _ _) he0
  have he2n : 0 ≤ fx C.e2 := le_trans (edist2_nonneg _ _) he2
  -- the vertex radii
  have hCeps : C.epsR = [epsCell (mkRing g ir) ad.ch + C.e0 + 1, 0, epsCell (mkRing g ir2) ad.ch + C.e2 + 1] := by
    rw [← hR1, ← hR2]; rfl
  have hCe0i : 0 ≤ C.e0 := by rw [hCe0]; exact distHi_nonneg _ _ _ _
  have hCe2i : 0 ≤ C.e2 := by rw [hCe2]; exact distHi_nonneg _ _ _ _
  have hepsn : ∀ i, 0 ≤ epsOf C i := by
    intro i
    unfold epsOf
    apply fx_nonneg_iff.mpr
    fin_cases i <;> simp only [hCeps, Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, List.getD_cons_zero,
      List.getD_cons_succ]
    · linarith [epsCell_nonneg (mkRing g ir) ad.ch]
    · exact le_rfl
    · linarith [epsCell_nonneg (mkRing g ir2) ad.ch]
  have hepsZ : ∀ w ∈ sector r1 r2 0 h, edist2 w CZ ≤ fx (epsCell (mkRing g ir) ad.ch) := by
    intro w hw
    have := hDS.2.1 (mkRing g ir) ad.ch r1 r2 0 h m1r1 m1r2 m1rho mch hZ.1 hZ.2.1 hhpos
      (by have := hZ.2.2.2.2.2; rwa [sub_zero] at this) (by linarith [Real.pi_pos])
      (by rw [zero_add]; exact hZ.2.2.2.2.1)
    simp only [zero_add] at this
    exact this w hw
  have hepsZ' : ∀ z ∈ sector q1 q2 (d * h) ((d + 1) * h), edist2 z CZ' ≤ fx (epsCell (mkRing g ir2) ad.ch) := by
    intro z hz
    have e1 : (d + 1 : ℝ) * h = d * h + h := by ring
    have := hDS.2.1 (mkRing g ir2) ad.ch q1 q2 (d * h) h m2r1 m2r2 m2rho mch hZ'.1 hZ'.2.1 hhpos
      (by have := hZ'.2.2.2.2.2; rwa [e1, add_sub_cancel_left] at this) hZ'.2.2.1 (by rw [← e1]; exact hZ'.2.2.2.2.1)
    rw [← e1] at this
    exact this z hz
  have heps : ∀ w ∈ sector r1 r2 0 h, ∀ z ∈ sector q1 q2 (d * h) ((d + 1) * h), ∀ i,
      enorm2 (![-w, (0 : Pt), z] i - c i) ≤ epsOf C i := by
    intro w hw z hz i
    fin_cases i
    · show enorm2 (-w - c 0) ≤ fx (C.epsR.getD 0 0)
      rw [hCeps]
      simp only [List.getD_cons_zero]
      have e1 : -w - c 0 = -(w - -c 0) := by abel
      rw [e1, enorm2_neg, ← edist2_eq, fx_add, fx_add]
      linarith [edist2_triangle w CZ (-c 0), hepsZ w hw, fx_one_pos]
    · show enorm2 ((0 : Pt) - c 1) ≤ fx (C.epsR.getD 1 0)
      rw [hc1, hCeps]
      simp only [List.getD_cons_succ, List.getD_cons_zero, sub_zero]
      unfold enorm2 fx; simp
    · show enorm2 (z - c 2) ≤ fx (C.epsR.getD 2 0)
      rw [hCeps]
      simp only [List.getD_cons_succ, List.getD_cons_zero]
      rw [← edist2_eq, fx_add, fx_add]
      linarith [edist2_triangle z CZ' (c 2), hepsZ' z hz, fx_one_pos]
  -- the distance bounds of the code
  have hCdmn : C.dmn = [(Iv.mul (mkRing g ir).r1 ad.ch).lo - (C.e0 + 1), (Iv.mul (mkRing g ir2).r1 ad.ch).lo - (C.e2 + 1),
      (Iv.sqrt ⟨Max.max (frange (Iv.mul (mkRing g ir).r1 ad.ch) (mkRing g ir).r2 (Iv.mul (mkRing g ir2).r1 ad.ch)
        (mkRing g ir2).r2 dd.cmin dd.cmax).1 0, Max.max (frange (Iv.mul (mkRing g ir).r1 ad.ch) (mkRing g ir).r2
        (Iv.mul (mkRing g ir2).r1 ad.ch) (mkRing g ir2).r2 dd.cmin dd.cmax).1 0⟩).lo - (C.e0 + C.e2 + 1)] := by
    rw [← hR1, ← hR2]; rfl
  have hCdmx : C.dmx = [(mkRing g ir).r2.hi + (C.e0 + 1), (mkRing g ir2).r2.hi + (C.e2 + 1),
      (Iv.sqrt ⟨(frange (Iv.mul (mkRing g ir).r1 ad.ch) (mkRing g ir).r2 (Iv.mul (mkRing g ir2).r1 ad.ch)
        (mkRing g ir2).r2 dd.cmin dd.cmax).2, (frange (Iv.mul (mkRing g ir).r1 ad.ch) (mkRing g ir).r2
        (Iv.mul (mkRing g ir2).r1 ad.ch) (mkRing g ir2).r2 dd.cmin dd.cmax).2⟩).hi + (C.e0 + C.e2 + 1)] := by
    rw [← hR1, ← hR2]; rfl
  set r1h := Iv.mul (mkRing g ir).r1 ad.ch with hr1h
  set q1h := Iv.mul (mkRing g ir2).r1 ad.ch with hq1h
  set hh := frange r1h (mkRing g ir).r2 q1h (mkRing g ir2).r2 dd.cmin dd.cmax with hhh
  have hmr1h : ivMem (r1 * Real.cos (h / 2)) r1h := Iv.mem_mul m1r1 mch
  have hmq1h : ivMem (q1 * Real.cos (h / 2)) q1h := Iv.mem_mul m2r1 mch
  -- Lemma 4 on the hulls (T2, T3)
  have hF : ∀ ρ φ ρ' φ' : ℝ, r1 * Real.cos (h / 2) ≤ ρ → ρ ≤ r2 → 0 ≤ φ → φ ≤ h →
      q1 * Real.cos (h / 2) ≤ ρ' → ρ' ≤ q2 → d * h ≤ φ' → φ' ≤ (d + 1) * h →
      fx hh.1 ≤ ρ ^ 2 + ρ' ^ 2 + 2 * ρ * ρ' * Real.cos (φ' - φ) ∧
      ρ ^ 2 + ρ' ^ 2 + 2 * ρ * ρ' * Real.cos (φ' - φ) ≤ fx hh.2 := by
    intro ρ φ ρ' φ' hρ1 hρ2 hφ1 hφ2 hρ'1 hρ'2 hφ'1 hφ'2
    obtain ⟨hc1, hc2⟩ := hAR h d g.NT hhpos hNh hd φ φ' hφ1 hφ2 hφ'1 hφ'2
    have hc2' : (if |d| ≤ 1 then (1 : ℝ) else Real.cos ((|d| - 1) * h)) ≤ 1 := by
      split_ifs; exacts [le_rfl, Real.cos_le_one _]
    exact hFS r1h (mkRing g ir).r2 q1h (mkRing g ir2).r2 dd.cmin dd.cmax (r1 * Real.cos (h / 2)) r2
      (q1 * Real.cos (h / 2)) q2 _ _ hmr1h m1r2 hmq1h m2r2 mcmin mcmax (mul_nonneg hZ.1 hcosh)
      (mul_nonneg hZ'.1 hcosh) (Real.neg_one_le_cos _) hc2' ρ ρ' (Real.cos (φ' - φ)) hρ1 hρ2 hρ'1 hρ'2 hc1 hc2
  -- segment points
  have hsegX : ∀ w : Pt, ∀ t : ℝ, segPt (c 0) (-w) t = -((-c 0) + t • (w - (-c 0))) := by
    intro w t; rw [segPt_eq]; ext <;> simp <;> ring
  have hsegO : ∀ t : ℝ, segPt (c 1) (0 : Pt) t = 0 := by intro t; rw [segPt_eq, hc1]; simp
  have hsegY : ∀ z : Pt, ∀ t : ℝ, segPt (c 2) z t = c 2 + t • (z - c 2) := fun z t => rfl
  have hcos0 : Real.cos ((h - 0) / 2) = Real.cos (h / 2) := by rw [sub_zero]
  have hcos1 : Real.cos (((d + 1) * h - d * h) / 2) = Real.cos (h / 2) := by congr 1; ring
  have hseg : ∀ w ∈ sector r1 r2 0 h, ∀ z ∈ sector q1 q2 (d * h) ((d + 1) * h), ∀ i j : Fin 3, i < j →
      ∀ t ∈ Icc (0 : ℝ) 1,
        dloOf C i j ≤ edist2 (segPt (c i) (![-w, (0 : Pt), z] i) t) (segPt (c j) (![-w, (0 : Pt), z] j) t) ∧
        edist2 (segPt (c i) (![-w, (0 : Pt), z] i) t) (segPt (c j) (![-w, (0 : Pt), z] j) t) ≤ dhiOf C i j := by
    intro w hw z hz i j hij t ht
    obtain ⟨hX1, hX2⟩ := seg_norm hZ hw ht (-c 0) he0
    obtain ⟨hY1, hY2⟩ := seg_norm hZ' hz ht (c 2) he2
    rw [hcos0] at hX1
    rw [hcos1] at hY1
    fin_cases i <;> fin_cases j <;> simp only [Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
      Fin.reduceLT, lt_self_iff_false, not_lt_zero', Nat.lt_irrefl] at hij ⊢
    all_goals first | exact absurd hij (by decide) | skip
    · -- (0, 1)
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      rw [hsegX, hsegO, edist2_zero_right, enorm2_neg]
      unfold dloOf dhiOf pIdx
      simp only [Fin.isValue, Fin.val_zero, Fin.val_one, and_self, if_true, hCdmn, hCdmx, List.getD_cons_zero]
      rw [fx_sub, fx_add, fx_add, fx_add]
      have := ivMem_lo_le hmr1h
      have := ivMem_hi_le m1r2
      constructor <;> linarith [fx_one_pos]
    · -- (0, 2)
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      rw [hsegX, hsegY]
      obtain ⟨ρ, φ, hρ1, hρ2, hφ1, hφ2, hXP⟩ := seg_hull hZ hw ht (-c 0) he0
      obtain ⟨ρ', φ', hρ'1, hρ'2, hφ'1, hφ'2, hYQ⟩ := seg_hull hZ' hz ht (c 2) he2
      have hρ1' : r1 * Real.cos (h / 2) ≤ ρ := by simpa using hρ1
      have hρ'1' : q1 * Real.cos (h / 2) ≤ ρ' := by
        convert hρ'1 using 3; ring
      have hφ1' : 0 ≤ φ := by simpa using hφ1
      have hφ2' : φ ≤ h := by simpa using hφ2
      obtain ⟨hF1, hF2⟩ := hF ρ φ ρ' φ' hρ1' hρ2 hφ1' hφ2' hρ'1' hρ'2 hφ'1 hφ'2
      set X := -c 0 + t • (w - -c 0)
      set Y := c 2 + t • (z - c 2)
      set P : Pt := (ρ * Real.cos φ, ρ * Real.sin φ)
      set Q : Pt := (ρ' * Real.cos φ', ρ' * Real.sin φ')
      have hPQ := enorm2_polar_add_sq ρ φ ρ' φ'
      have hdist : edist2 (-X) Y = enorm2 (X + Y) := by
        rw [edist2_eq, show -X - Y = -(X + Y) by abel, enorm2_neg]
      rw [hdist]
      have hdiff : |enorm2 (X + Y) - enorm2 (P + Q)| ≤ fx C.e0 + fx C.e2 := by
        refine (abs_enorm2_sub_le _ _).trans ?_
        rw [show X + Y - (P + Q) = (X - P) + (Y - Q) by abel]
        exact (enorm2_add_le _ _).trans (add_le_add hXP hYQ)
      have hnn : 0 ≤ enorm2 (P + Q) := enorm2_nonneg _
      have hlo : √(fx (Max.max hh.1 0)) ≤ enorm2 (P + Q) := by
        rw [fx_max, show fx (0 : ℤ) = 0 by unfold fx; simp]
        calc √(max (fx hh.1) 0) ≤ √(enorm2 (P + Q) ^ 2) :=
              Real.sqrt_le_sqrt (max_le (by rw [hPQ]; exact hF1) (sq_nonneg _))
          _ = enorm2 (P + Q) := Real.sqrt_sq hnn
      have hhi : enorm2 (P + Q) ≤ √(fx hh.2) := by
        calc enorm2 (P + Q) = √(enorm2 (P + Q) ^ 2) := (Real.sqrt_sq hnn).symm
          _ ≤ √(fx hh.2) := Real.sqrt_le_sqrt (by rw [hPQ]; exact hF2)
      have hsl := sqrt_pt_lo (Max.max hh.1 0)
      have hsh := sqrt_pt_hi hh.2
      unfold dloOf dhiOf pIdx
      simp only [Fin.isValue, Fin.val_zero, Fin.val_two, Fin.val_one, hCdmn, hCdmx, List.getD_cons_succ,
        List.getD_cons_zero]
      norm_num
      rw [fx_sub, fx_add, fx_add, fx_add, fx_add, fx_add]
      have habs := abs_le.mp hdiff
      constructor <;> linarith [fx_one_pos]
    · -- (1, 2)
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      rw [hsegO, hsegY, edist2_comm, edist2_zero_right]
      unfold dloOf dhiOf pIdx
      simp only [Fin.isValue, Fin.val_one, Fin.val_two, hCdmn, hCdmx, List.getD_cons_succ, List.getD_cons_zero]
      norm_num
      rw [fx_sub, fx_add, fx_add, fx_add]
      have := ivMem_lo_le hmq1h
      have := ivMem_hi_le m2r2
      constructor <;> linarith [fx_one_pos]
  -- the union area at the expansion point (module B)
  have hU0 : unionArea c ≤ fx ur.A.hi :=
    ivMem_hi_le (unionSound hG cosSin cosSin_sound unionCand 3 C.pts ur rfl hur).1
  -- the pairs of the fold
  obtain ⟨hpp, her_eq⟩ := fold_spec g.prune C her
  have hpI : ∀ i j : Fin 3, pIdx i j < 3 := by intro i j; unfold pIdx; split_ifs <;> omega
  have hdlo_pos : ∀ i j : Fin 3, i < j → 0 < dloOf C i j := by
    intro i j _
    unfold dloOf
    rcases hpp _ (hpI i j) with h2 | h0
    · apply fx_pos_iff.mpr
      have : (0 : ℤ) < 2 * ONE := by norm_num [ONE, PR]
      omega
    · exact fx_pos_iff.mpr h0
  have hfirst_dhi : ∀ i j : Fin 3, i < j → firstOf C i j = true → dhiOf C i j < 2 := by
    intro i j _ hf
    unfold firstOf at hf
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hf
    exact useFirst_dhi hf.2
  -- T6
  have hPMres := hPM hV (sector r1 r2 0 h) (sector q1 q2 (d * h) ((d + 1) * h)) c (epsOf C) (dloOf C)
    (dhiOf C) (firstOf C) (fx ur.A.hi) (fx C.e0) (fx C.e2) (fx (mkRing g ir).momHi) (fx (mkRing g ir2).momHi)
    (measurableSet_sector hZ) (measurableSet_sector hZ') (sector_ne_zero hZ) (sector_ne_top hZ)
    (sector_ne_zero hZ') (sector_ne_top hZ') (sector_bounded hZ.1) (sector_bounded hZ'.1) hc1 hdlo_pos
    hfirst_dhi hseg heps hU0 (by rw [hcenZ]; exact he0) (by rw [hcenZ']; exact he2) hM0 hM2
  -- the nondegeneracy tests of the three pairs
  have hokp : pairOK g.prune C 0 = true ∧ pairOK g.prune C 1 = true ∧ pairOK g.prune C 2 = true := by
    unfold entryOK at hok
    dsimp only at hok
    rw [← hC, hur] at hok
    simp only [Bool.and_eq_true] at hok
    exact ⟨hok.1.1, hok.1.2, hok.2⟩
  -- moments of the code
  have hCS1 : C.S1s = [(Iv.sqrt ⟨(mkRing g ir).momHi + shrU (C.e0 * C.e0) PR + 1,
        (mkRing g ir).momHi + shrU (C.e0 * C.e0) PR + 1⟩).hi,
      (Iv.sqrt ⟨(mkRing g ir2).momHi + shrU (C.e2 * C.e2) PR + 1,
        (mkRing g ir2).momHi + shrU (C.e2 * C.e2) PR + 1⟩).hi,
      (Iv.sqrt ⟨(mkRing g ir).momHi + shrU (C.e0 * C.e0) PR + 1,
        (mkRing g ir).momHi + shrU (C.e0 * C.e0) PR + 1⟩).hi +
      (Iv.sqrt ⟨(mkRing g ir2).momHi + shrU (C.e2 * C.e2) PR + 1,
        (mkRing g ir2).momHi + shrU (C.e2 * C.e2) PR + 1⟩).hi] := by rw [← hR1, ← hR2]; rfl
  have hCS2 : C.S2s = [(mkRing g ir).momHi + shrU (C.e0 * C.e0) PR + 1,
      (mkRing g ir2).momHi + shrU (C.e2 * C.e2) PR + 1,
      (mkRing g ir).momHi + shrU (C.e0 * C.e0) PR + 1 + ((mkRing g ir2).momHi + shrU (C.e2 * C.e2) PR + 1) +
        2 * shrU ((Iv.sqrt ⟨(mkRing g ir).momHi + shrU (C.e0 * C.e0) PR + 1,
          (mkRing g ir).momHi + shrU (C.e0 * C.e0) PR + 1⟩).hi *
          (Iv.sqrt ⟨(mkRing g ir2).momHi + shrU (C.e2 * C.e2) PR + 1,
          (mkRing g ir2).momHi + shrU (C.e2 * C.e2) PR + 1⟩).hi) PR + 2] := by rw [← hR1, ← hR2]; rfl
  have hS := S12_spec (mom0 := (mkRing g ir).momHi) (mom2 := (mkRing g ir2).momHi) (e0 := C.e0) (e2 := C.e2)
    le_rfl le_rfl hM0n hM2n
  set M0' := fx (mkRing g ir).momHi + fx C.e0 ^ 2 with hM0'
  set M2' := fx (mkRing g ir2).momHi + fx C.e2 ^ 2 with hM2'
  have hM0'n : 0 ≤ M0' := by positivity
  have hM2'n : 0 ≤ M2' := by positivity
  have hS1n : ∀ i j : Fin 3, 0 ≤ pairS1 M0' M2' i j := by
    intro i j; unfold pairS1; split_ifs <;> positivity
  have hS2n : ∀ i j : Fin 3, 0 ≤ pairS2 M0' M2' i j := by
    intro i j; unfold pairS2; split_ifs <;> positivity
  -- a point of the pair (for d⁻ ≤ d⁺)
  obtain ⟨w0, hw0⟩ := nonempty_of_measure_ne_zero (sector_ne_zero hZ)
  obtain ⟨z0, hz0⟩ := nonempty_of_measure_ne_zero (sector_ne_zero hZ')
  have hdle : ∀ i j : Fin 3, i < j → dloOf C i j ≤ dhiOf C i j := by
    intro i j hij
    obtain ⟨h1, h2⟩ := hseg w0 hw0 z0 hz0 i j hij 0 ⟨le_rfl, zero_le_one⟩
    linarith
  -- one pair: the real term is at most the code's
  have hterm : ∀ (i j l : Fin 3) (p : ℕ), i < j → pairIJL p = (i.val, j.val, l.val) → l ≠ i → l ≠ j →
      pIdx i j = p → pairS1 M0' M2' i j ≤ fx (C.S1s.getD p 0) → pairS2 M0' M2' i j ≤ fx (C.S2s.getD p 0) →
      pairOK g.prune C p = true →
      (if dloOf C i j < 2 then
        (nuCountSeg c (epsOf C) (dloOf C) (dhiOf C) (firstOf C) i j : ℝ) *
          pairRem (dloOf C i j) (dhiOf C i j) (firstOf C i j) (pairS1 M0' M2' i j) (pairS2 M0' M2' i j)
      else 0) ≤ fx (if 2 * ONE ≤ C.dmn.getD p 0 then 0 else pairTerm g.prune C p) := by
    intro i j l p hij hijl hli hlj hpIdx hS1 hS2 hokp1
    have hp3 : p < 3 := hpIdx ▸ hpI i j
    have hdlo : dloOf C i j = fx (C.dmn.getD p 0) := by unfold dloOf; rw [hpIdx]
    have hdhi : dhiOf C i j = fx (C.dmx.getD p 0) := by unfold dhiOf; rw [hpIdx]
    by_cases h2 : 2 * ONE ≤ C.dmn.getD p 0
    · rw [if_pos h2]
      have : ¬ dloOf C i j < 2 := by
        rw [hdlo]; have := fx_mono h2; rw [fx_two_ONE] at this; linarith
      rw [if_neg this]; unfold fx; simp
    · rw [if_neg h2]
      have hdn : 0 < C.dmn.getD p 0 := (hpp p hp3).resolve_left h2
      have hlt : dloOf C i j < 2 := by
        rw [hdlo]; have := fx_lt_of (not_le.mp h2); rwa [fx_two_ONE] at this
      rw [if_pos hlt]
      obtain ⟨hpos, hnd⟩ := pairOK_spec hokp1 h2 hdn hijl
      have hfirst : firstOf C i j = decide (useFirstOf (C.dmx.getD p 0)) := by
        unfold firstOf; rw [hpIdx, decide_eq_true (not_le.mp h2), Bool.true_and]
      have hnu := nu_spec hDS g.prune C c (fun _ => rfl) (epsOf C) (fun _ => rfl) hepsn (dloOf C) (dhiOf C)
        (firstOf C) p i j l hijl hli hlj hdn hdlo hdhi hfirst hpos hnd
      have hrt := radTang_spec hdn hpos hS1 hS2 (hS1n i j) (hS2n i j)
      rw [← hdlo, ← hdhi, ← hfirst] at hrt
      have hRnn := pairRem_nonneg (first := firstOf C i j) (hdlo_pos i j hij) (hdle i j hij) hlt
        (hfirst_dhi i j hij) (hS1n i j) (hS2n i j)
      unfold pairTerm
      simp only
      rw [fx_natMul]
      calc (nuCountSeg c (epsOf C) (dloOf C) (dhiOf C) (firstOf C) i j : ℝ) *
            pairRem (dloOf C i j) (dhiOf C i j) (firstOf C i j) (pairS1 M0' M2' i j) (pairS2 M0' M2' i j)
          ≤ (nuOf g.prune C.pts (if g.prune then C.epsR else [0, 0, 0]) (lamOf (C.dmx.getD p 0))
              (muOf (C.dmn.getD p 0) (C.dmx.getD p 0)) (C.dmn.getD p 0) p : ℝ) *
            pairRem (dloOf C i j) (dhiOf C i j) (firstOf C i j) (pairS1 M0' M2' i j) (pairS2 M0' M2' i j) :=
            mul_le_mul_of_nonneg_right (by exact_mod_cast hnu) hRnn
        _ ≤ _ := mul_le_mul_of_nonneg_left hrt (Nat.cast_nonneg _)
  -- the remainder sum (T6) is at most the code's `er`
  simp only at hS
  obtain ⟨hS01, -, -⟩ := hS 0 1
  obtain ⟨-, hS12, -⟩ := hS 1 2
  obtain ⟨-, -, hS02⟩ := hS 0 2
  have t01 := hterm 0 1 2 0 (by decide) rfl (by decide) (by decide) (by decide)
    (by rw [hCS1]; exact (hS01 ⟨rfl, rfl⟩).1) (by rw [hCS2]; exact (hS01 ⟨rfl, rfl⟩).2) hokp.1
  have t12 := hterm 1 2 0 1 (by decide) rfl (by decide) (by decide) (by decide)
    (by rw [hCS1]; exact (hS12 ⟨rfl, rfl⟩).1) (by rw [hCS2]; exact (hS12 ⟨rfl, rfl⟩).2) hokp.2.1
  have t02 := hterm 0 2 1 2 (by decide) rfl (by decide) (by decide) (by decide)
    (by rw [hCS1]; exact (hS02 ⟨rfl, rfl⟩).1) (by rw [hCS2]; exact (hS02 ⟨rfl, rfl⟩).2) hokp.2.2
  have hrem : (∑ i : Fin 3, ∑ j : Fin 3, (if i < j ∧ dloOf C i j < 2 then
        (nuCountSeg c (epsOf C) (dloOf C) (dhiOf C) (firstOf C) i j : ℝ) *
          pairRem (dloOf C i j) (dhiOf C i j) (firstOf C i j) (pairS1 M0' M2' i j) (pairS2 M0' M2' i j)
      else 0)) ≤ fx er := by
    rw [her_eq, fx_finset_sum, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
    simp only [Fin.sum_univ_three]
    have l00 : ¬ ((0 : Fin 3) < 0) := by decide
    have l10 : ¬ ((1 : Fin 3) < 0) := by decide
    have l11 : ¬ ((1 : Fin 3) < 1) := by decide
    have l20 : ¬ ((2 : Fin 3) < 0) := by decide
    have l21 : ¬ ((2 : Fin 3) < 1) := by decide
    have l22 : ¬ ((2 : Fin 3) < 2) := by decide
    have l01 : (0 : Fin 3) < 1 := by decide
    have l02 : (0 : Fin 3) < 2 := by decide
    have l12 : (1 : Fin 3) < 2 := by decide
    simp only [l00, l10, l11, l20, l21, l22, l01, l02, l12, false_and, true_and, if_false, add_zero, zero_add]
    linarith
  -- `∫∫ A(-w, 0, z) = ∫∫ A_2 + π |Z| |Z'| + |Z| |Z'| meanA1`
  have hvZ := volume_sector_pos hZ
  have hvZ' := volume_sector_pos hZ'
  have hne := sector_ne_top hZ
  have hne' := sector_ne_top hZ'
  have hconst : IntegrableOn (fun _ : Pt × Pt => π) (sector r1 r2 0 h ×ˢ sector q1 q2 (d * h) ((d + 1) * h)) :=
    integrableOn_bdd (volume_prod_ne_top hne hne') measurable_const (M := π) fun _ => by
      rw [abs_of_pos Real.pi_pos]
  have hint_U : ∫ p in sector r1 r2 0 h ×ˢ sector q1 q2 (d * h) ((d + 1) * h), unionArea ![-p.1, (0 : Pt), p.2] =
      (∫ p in sector r1 r2 0 h ×ˢ sector q1 q2 (d * h) ((d + 1) * h), A2 p.1 p.2) +
        π * ((volume (sector r1 r2 0 h)).toReal * (volume (sector q1 q2 (d * h) ((d + 1) * h))).toReal) +
        (volume (sector r1 r2 0 h)).toReal * (volume (sector q1 q2 (d * h) ((d + 1) * h))).toReal *
          meanA1 r1 r2 := by
    have e : (fun p : Pt × Pt => unionArea ![-p.1, (0 : Pt), p.2]) = fun p => (A2 p.1 p.2 + π) + A1 p.1 := by
      funext p; rw [hA2]; ring
    have hi1 : IntegrableOn (fun p : Pt × Pt => A2 p.1 p.2 + π)
        (sector r1 r2 0 h ×ˢ sector q1 q2 (d * h) ((d + 1) * h)) := (integrableOn_A2 hne hne').add hconst
    have hsplit : ∫ p in sector r1 r2 0 h ×ˢ sector q1 q2 (d * h) ((d + 1) * h), (A2 p.1 p.2 + π + A1 p.1) =
        (∫ p in sector r1 r2 0 h ×ˢ sector q1 q2 (d * h) ((d + 1) * h), (A2 p.1 p.2 + π)) +
          ∫ p in sector r1 r2 0 h ×ˢ sector q1 q2 (d * h) ((d + 1) * h), A1 p.1 :=
      integral_add hi1 (integrableOn_A1_fst hne hne')
    have hsplit2 : ∫ p in sector r1 r2 0 h ×ˢ sector q1 q2 (d * h) ((d + 1) * h), (A2 p.1 p.2 + π) =
        (∫ p in sector r1 r2 0 h ×ˢ sector q1 q2 (d * h) ((d + 1) * h), A2 p.1 p.2) +
          ∫ _p in sector r1 r2 0 h ×ˢ sector q1 q2 (d * h) ((d + 1) * h), π :=
      integral_add (integrableOn_A2 hne hne') hconst
    rw [e, hsplit, hsplit2, setIntegral_const, setIntegral_fst', integral_A1_sector hG hA1 hZ, smul_eq_mul,
      Measure.real, Measure.volume_eq_prod, Measure.prod_prod, ENNReal.toReal_mul]
    ring
  rw [hint_U] at hPMres
  have hpi := piLo_le
  have hfx2 : 0 ≤ fx 2 := by unfold fx; positivity
  have key : fx ur.A.hi + 2 * (fx C.e0 + fx C.e2) +
      (∑ i : Fin 3, ∑ j : Fin 3, (if i < j ∧ dloOf C i j < 2 then
        (nuCountSeg c (epsOf C) (dloOf C) (dhiOf C) (firstOf C) i j : ℝ) *
          pairRem (dloOf C i j) (dhiOf C i j) (firstOf C i j) (pairS1 M0' M2' i j) (pairS2 M0' M2' i j)
      else 0)) - π - meanA1 r1 r2 ≤
      fx (ur.A.hi + 2 * (C.e0 + C.e2) + er - (piLo + (mkRing g ir).euLo) + 2) := by
    rw [fx_add, fx_sub, fx_add, fx_add, fx_mul_two, fx_add, fx_add]
    linarith
  have hV : 0 < (volume (sector r1 r2 0 h)).toReal * (volume (sector q1 q2 (d * h) ((d + 1) * h))).toReal :=
    mul_pos hvZ hvZ'
  have hmul := mul_le_mul_of_nonneg_right key hV.le
  linarith

end BHH.W2
