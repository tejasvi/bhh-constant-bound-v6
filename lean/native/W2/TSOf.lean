/-
`TableSoundOf` (W2/TSProps.lean): the table soundness of a production run from the entry bound and the facts T1
(rings), T2 (angles), T3 (Lemma 4), T5 (`A_1` radial) and T7 (rotations).
-/
import W2.TSProps
import W2.EntryGeo
import W2.DiscCells

open MeasureTheory Set Real
open scoped ENNReal

noncomputable section

namespace BHH.W2.TSO

open W2C BHH.Cert BHH BHH.W2

lemma rad_lt_succ (g : W2C.Grid) (h1 : 0 < g.N1) (h2 : 0 < g.N2) (j : ℕ) :
    (gR g).rad j < (gR g).rad (j + 1) := by
  have hN1 : (0 : ℝ) < g.N1 := by exact_mod_cast h1
  have hN2 : (0 : ℝ) < g.N2 := by exact_mod_cast h2
  show GridR.rad ⟨g.N1, g.N2, g.NT⟩ j < GridR.rad ⟨g.N1, g.N2, g.NT⟩ (j + 1)
  unfold GridR.rad
  simp only
  by_cases hj : j + 1 ≤ g.N1
  · have hj' : j ≤ g.N1 := by omega
    rw [if_pos hj', if_pos hj]
    apply div_lt_div_of_pos_right _ hN1
    push_cast; linarith
  · by_cases hj' : j ≤ g.N1
    · rw [if_pos hj', if_neg hj]
      have e : j = g.N1 := by omega
      subst e
      rw [div_self hN1.ne']
      have : (0 : ℝ) < ((g.N1 + 1 - g.N1 : ℕ) : ℝ) / g.N2 := by
        apply div_pos _ hN2; norm_num
      linarith
    · rw [if_neg hj', if_neg hj]
      have e : ((j + 1 - g.N1 : ℕ) : ℝ) = ((j - g.N1 : ℕ) : ℝ) + 1 := by
        have : j + 1 - g.N1 = (j - g.N1) + 1 := by omega
        rw [this]; push_cast; ring
      rw [e, add_div]
      have : (0 : ℝ) < 1 / g.N2 := by positivity
      linarith

lemma ang_succ (g : W2C.Grid) (it : ℕ) : (gR g).ang (it + 1) = (gR g).ang it + π / g.NT := by
  show GridR.ang ⟨g.N1, g.N2, g.NT⟩ (it + 1) = GridR.ang ⟨g.N1, g.N2, g.NT⟩ it + π / g.NT
  unfold GridR.ang; simp only; push_cast; ring

lemma secOK_cell (g : W2C.Grid) (h1 : 0 < g.N1) (h2 : 0 < g.N2) (hNT : 2 ≤ g.NT) (ir : ℕ) {it : ℕ}
    (hit : it < g.NT) :
    SecOK ((gR g).rad ir) ((gR g).rad (ir + 1)) ((gR g).ang it) ((gR g).ang (it + 1)) := by
  have hNT0 : 0 < (gR g).NT := by show 0 < g.NT; omega
  have hN : (2 : ℝ) ≤ g.NT := by exact_mod_cast hNT
  refine ⟨(gR g).rad_nonneg ir, rad_lt_succ g h1 h2 ir, ?_, (gR g).ang_lt hNT0 (Nat.lt_succ_self it), ?_, ?_⟩
  · have := (gR g).ang_ge hNT0 it; linarith [Real.pi_pos]
  · have := (gR g).ang_le hNT0 (show it + 1 ≤ (gR g).NT from hit); linarith [Real.pi_pos]
  · rw [ang_succ]
    have : π / g.NT ≤ π / 2 := div_le_div_of_nonneg_left Real.pi_pos.le (by norm_num) hN
    linarith

lemma cell_eq_sector (g : W2C.Grid) (ir it : ℕ) :
    (gR g).cell ir it = sector ((gR g).rad ir) ((gR g).rad (ir + 1)) ((gR g).ang it) ((gR g).ang (it + 1)) := rfl

lemma rings_get (g : W2C.Grid) (dtl : ℕ) {ir : ℕ} (hir : ir < g.NR) :
    (mkRunData g dtl true).rings[ir]! = mkRing g ir := by
  rw [mkRunData_rings, getElem!_map _ _ (by simpa using hir), range_getElem! hir]

/-- the class of a table entry is `1` exactly when Lemma 4's upper end is at most `1` -/
lemma entryF_fst (prune : Bool) (rings : Array Ring) (ad : AData) (dd : DData) (ir ir2 : ℕ) :
    (entryF prune rings ad dd ir ir2).1 =
      (if (frange rings[ir]!.r1 rings[ir]!.r2 rings[ir2]!.r1 rings[ir2]!.r2 dd.cmin dd.cmax).2 ≤ ONE then 1
       else if ONE < (frange rings[ir]!.r1 rings[ir]!.r2 rings[ir2]!.r1 rings[ir2]!.r2 dd.cmin dd.cmax).1 then 0
       else 2) := by
  unfold entryF
  simp only
  split
  · rfl
  · split <;> rfl

lemma mkDTab_get (g : W2C.Grid) {di : ℕ} (hdi : di < g.ND) :
    (mkDTab g)[di]! = mkDData g (Int.ofNat di - Int.ofNat (g.NT - 1)) := by
  unfold mkDTab
  rw [getElem!_map _ _ (by simpa using hdi), range_getElem! hdi]

/-- the table entry of the cell pair `(ir, ir2)` at offset `d` -/
lemma tab_entry (g : W2C.Grid) (dtl : ℕ) {ir ir2 : ℕ} (hir : ir < g.NR) (hir2 : ir2 < g.NR) {it it2 : ℕ}
    (hit : it < g.NT) (hit2 : it2 < g.NT) :
    (mkRunData g dtl true).tab[tidx g ir ir2 ((it2 : ℤ) - it)]! =
      prepE dtl (entryF g.prune ((Array.range g.NR).map (mkRing g)) (mkAData g) (mkDData g ((it2 : ℤ) - it))
        ir ir2) := by
  have hND : g.ND = 2 * g.NT - 1 := rfl
  set di := (((it2 : ℤ) - it) + ((g.NT - 1 : ℕ) : ℤ)).toNat with hdi
  have hdi' : di = it2 + (g.NT - 1) - it := toNat_off it2 it g.NT hit
  have hdiND : di < g.ND := by rw [hdi', hND]; omega
  have hidx : tidx g ir ir2 ((it2 : ℤ) - it) = ir * (g.NR * g.ND) + (ir2 * g.ND + di) := by
    unfold tidx; rw [← hdi]; ring
  have hlt : ir2 * g.ND + di < g.NR * g.ND := by nlinarith
  have hbound : tidx g ir ir2 ((it2 : ℤ) - it) < g.NR * g.NR * g.ND := by
    rw [hidx]; nlinarith
  rw [tab_getElem g dtl true hbound, hidx, flat_div _ _ hlt, flat_mod _ _ hlt, Nat.add_comm (ir2 * g.ND) di,
    Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hdiND, Nat.add_mul_div_right _ _ (by rw [hND]; omega),
    Nat.div_eq_of_lt hdiND, zero_add, mkDTab_get g hdiND]
  congr 3
  rw [hdi']
  have : it ≤ it2 + (g.NT - 1) := by omega
  simp only [Int.ofNat_eq_natCast]
  push_cast [Nat.cast_sub this, Nat.cast_sub (by omega : 1 ≤ g.NT)]
  ring

theorem tableSoundOf : TableSoundOf := by
  intro hG hRS hAS hAR hFR hA1 hRot g dtl h1 h2 hNT hNTb hNSUB hring hEB
  have hNR : (gR g).NR = g.NR := rfl
  have hNTe : (gR g).NT = g.NT := rfl
  -- ring facts
  have hRing : ∀ j, j < g.NR → _ := fun j hj => by
    have hok := hring j hj
    unfold ringOK at hok
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
    exact hRS g h1 h2 hNT hNSUB j hj hok.1 hok.2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- w_nonneg
    intro ir; unfold discOf; simp only; positivity
  · -- w_le
    intro ir it hir hit
    rw [hNR] at hir; rw [hNTe] at hit
    obtain ⟨-, -, harea, -⟩ := hRing ir hir
    unfold discOf; simp only
    rw [rings_get g dtl hir, cell_eq_sector, volume_sector_toReal (secOK_cell g h1 h2 hNT ir hit), ang_succ]
    by_cases ha : 0 ≤ (mkRing g ir).areaLo
    · have e : (((mkRing g ir).areaLo.toNat : ℕ) : ℝ) = ((mkRing g ir).areaLo : ℝ) := by
        exact_mod_cast Int.toNat_of_nonneg ha
      rw [e]
      have : fx (mkRing g ir).areaLo = ((mkRing g ir).areaLo : ℝ) / 2 ^ PR := rfl
      rw [← this]
      convert harea using 1; ring
    · push_neg at ha
      rw [Int.toNat_of_nonpos ha.le]
      have := (secOK_cell g h1 h2 hNT ir hit)
      have h0 := rad_lt_succ g h1 h2 ir
      have hr0 := (gR g).rad_nonneg ir
      have : 0 < (gR g).rad (ir + 1) ^ 2 - (gR g).rad ir ^ 2 := by nlinarith
      have hNT0 : 0 < g.NT := by omega
      have hNTr : (0 : ℝ) < g.NT := by exact_mod_cast hNT0
      have : 0 < π / g.NT := div_pos Real.pi_pos hNTr
      simp only [Nat.cast_zero, zero_div]
      nlinarith
  · -- ub
    intro ir it hir hit
    rw [hNR] at hir; rw [hNTe] at hit
    obtain ⟨-, -, -, -, -, -, heu, -⟩ := hRing ir hir
    unfold discOf; simp only
    rw [rings_get g dtl hir, cell_eq_sector, integral_A1_sector hG hA1 (secOK_cell g h1 h2 hNT ir hit)]
    have hv := ENNReal.toReal_nonneg (a := volume (sector ((gR g).rad ir) ((gR g).rad (ir + 1)) ((gR g).ang it)
      ((gR g).ang (it + 1))))
    rw [mul_comm]
    apply mul_le_mul_of_nonneg_right _ hv
    exact le_trans heu (fx_le_iff.mpr (le_ubInt _ _))
  · -- ab
    intro ir ir2 it it2 hir hir2 hit hit2
    rw [hNR] at hir hir2; rw [hNTe] at hit hit2
    have hNT0 : 0 < g.NT := by omega
    have hNTr : (0 : ℝ) < g.NT := by exact_mod_cast hNT0
    have hh : 0 < π / g.NT := div_pos Real.pi_pos hNTr
    set h := π / g.NT with hh_def
    set d : ℤ := (it2 : ℤ) - it with hd
    have hdlt : |d| < g.NT := by
      rw [hd, abs_lt]; constructor <;> omega
    have hdr : (d : ℝ) = (it2 : ℝ) - it := by rw [hd]; push_cast; ring
    -- the table entry
    have hab : (discOf g (mkRunData g dtl true).rings (mkRunData g dtl true).tab dtl).ab ir ir2 d =
        fx (ubInt (max (entryF g.prune ((Array.range g.NR).map (mkRing g)) (mkAData g) (mkDData g d) ir ir2).2 0)
          dtl) := by
      show fx (mkRunData g dtl true).tab[tidx g ir ir2 d]!.2 = _
      rw [hd, tab_entry g dtl hir hir2 hit hit2]
      rfl
    rw [hab]
    -- angles
    have hang : ∀ i : ℕ, (gR g).ang i = -(π / 2) + i * h := by
      intro i; show GridR.ang ⟨g.N1, g.N2, g.NT⟩ i = _; unfold GridR.ang; simp only; rw [hh_def]; ring
    have hNh : h * g.NT = π := by rw [hh_def]; field_simp
    have hitr : (it : ℝ) + 1 ≤ g.NT := by exact_mod_cast hit
    have hit2r : (it2 : ℝ) + 1 ≤ g.NT := by exact_mod_cast hit2
    have hit0 : (0 : ℝ) ≤ it := Nat.cast_nonneg _
    have hit20 : (0 : ℝ) ≤ it2 := Nat.cast_nonneg _
    -- rotation by -θ_it
    have hrot := hRot ((gR g).rad ir) ((gR g).rad (ir + 1)) ((gR g).ang it) ((gR g).ang (it + 1))
      ((gR g).rad ir2) ((gR g).rad (ir2 + 1)) ((gR g).ang it2) ((gR g).ang (it2 + 1)) (-(gR g).ang it)
      ((gR g).rad_nonneg ir) ((gR g).rad_nonneg ir2)
      (by rw [hang]; nlinarith [Real.pi_pos]) (by rw [hang]; push_cast; nlinarith [Real.pi_pos])
      (by rw [hang]; nlinarith [Real.pi_pos]) (by rw [hang]; push_cast; nlinarith [Real.pi_pos])
      (by linarith [Real.pi_pos]) (by rw [hang, hang]; push_cast; nlinarith [Real.pi_pos])
      (by rw [hang, hang]; nlinarith [Real.pi_pos]) (by rw [hang, hang]; push_cast; nlinarith [Real.pi_pos])
    have e1 : (gR g).ang it + -(gR g).ang it = 0 := by ring
    have e2 : (gR g).ang (it + 1) + -(gR g).ang it = π / g.NT := by rw [hang, hang]; push_cast; ring
    have e3 : (gR g).ang it2 + -(gR g).ang it = d * (π / g.NT) := by
      rw [hang, hang, hdr, ← hh_def]; ring
    have e4 : (gR g).ang (it2 + 1) + -(gR g).ang it = (d + 1) * (π / g.NT) := by
      rw [hang, hang, hdr, ← hh_def]; push_cast; ring
    rw [e1, e2, e3, e4] at hrot
    rw [cell_eq_sector, cell_eq_sector, hrot]
    -- the entry bound on the canonical pair
    have heb := hEB ir ir2 hir hir2 d hdlt
    have hok1 := secOK_cell g h1 h2 hNT ir hit
    have hok2 := secOK_cell g h1 h2 hNT ir2 hit2
    -- volumes of the cells = volumes of the canonical sectors
    have hv1 : (volume (sector ((gR g).rad ir) ((gR g).rad (ir + 1)) ((gR g).ang it) ((gR g).ang (it + 1)))).toReal =
        (volume (sector ((gR g).rad ir) ((gR g).rad (ir + 1)) 0 (π / g.NT))).toReal := by
      have hc : SecOK ((gR g).rad ir) ((gR g).rad (ir + 1)) 0 (π / g.NT) := by
        refine ⟨hok1.1, hok1.2.1, by linarith [Real.pi_pos], hh, ?_, ?_⟩
        · have : π / g.NT ≤ π / 2 := div_le_div_of_nonneg_left Real.pi_pos.le (by norm_num)
            (by exact_mod_cast hNT)
          linarith [Real.pi_pos]
        · have : π / g.NT ≤ π / 2 := div_le_div_of_nonneg_left Real.pi_pos.le (by norm_num)
            (by exact_mod_cast hNT)
          linarith
      rw [volume_sector_toReal hok1, volume_sector_toReal hc, ang_succ]; ring
    have hv2 : (volume (sector ((gR g).rad ir2) ((gR g).rad (ir2 + 1)) ((gR g).ang it2)
        ((gR g).ang (it2 + 1)))).toReal =
        (volume (sector ((gR g).rad ir2) ((gR g).rad (ir2 + 1)) (d * (π / g.NT)) ((d + 1) * (π / g.NT)))).toReal := by
      have hc : SecOK ((gR g).rad ir2) ((gR g).rad (ir2 + 1)) (d * (π / g.NT)) ((d + 1) * (π / g.NT)) := by
        have hdl : (-(g.NT : ℝ)) + 1 ≤ d := by rw [hdr]; linarith
        have hdu : (d : ℝ) + 1 ≤ g.NT := by rw [hdr]; linarith
        have hh2 : π / g.NT ≤ π / 2 := div_le_div_of_nonneg_left Real.pi_pos.le (by norm_num)
          (by exact_mod_cast hNT)
        refine ⟨hok2.1, hok2.2.1, ?_, by nlinarith, ?_, by nlinarith⟩
        · rw [← hh_def]; nlinarith
        · rw [← hh_def]; nlinarith
      rw [volume_sector_toReal hok2, volume_sector_toReal hc, ang_succ]; ring
    rw [hv1, hv2]
    refine le_trans heb ?_
    have hw1 := ENNReal.toReal_nonneg (a := volume (sector ((gR g).rad ir) ((gR g).rad (ir + 1)) 0 (π / g.NT)))
    have hw2 := ENNReal.toReal_nonneg (a := volume (sector ((gR g).rad ir2) ((gR g).rad (ir2 + 1)) (d * (π / g.NT))
      ((d + 1) * (π / g.NT))))
    apply mul_le_mul_of_nonneg_right _ hw2
    apply mul_le_mul_of_nonneg_right _ hw1
    exact fx_le_iff.mpr (le_trans (le_max_left _ _) (le_ubInt _ _))
  · -- sc
    intro ir ir2 it it2 hir hir2 hit hit2 hsc w hw z hz
    rw [hNR] at hir hir2; rw [hNTe] at hit hit2
    have hNT0 : 0 < g.NT := by omega
    have hNTr : (0 : ℝ) < g.NT := by exact_mod_cast hNT0
    have hh : 0 < π / g.NT := div_pos Real.pi_pos hNTr
    set h := π / g.NT with hh_def
    set d : ℤ := (it2 : ℤ) - it with hd
    have hdlt : |d| < g.NT := by
      rw [hd, abs_lt]; constructor <;> omega
    have hdr : (d : ℝ) = (it2 : ℝ) - it := by rw [hd]; push_cast; ring
    have hrg : ∀ j, j < g.NR → ((Array.range g.NR).map (mkRing g))[j]! = mkRing g j := fun j hj => by
      rw [getElem!_map _ _ (by simpa using hj), range_getElem! hj]
    -- the class of the entry is 1: Lemma 4's upper end is at most ONE
    have hfmax : (frange (mkRing g ir).r1 (mkRing g ir).r2 (mkRing g ir2).r1 (mkRing g ir2).r2
        (mkDData g d).cmin (mkDData g d).cmax).2 ≤ ONE := by
      have hs : ((mkRunData g dtl true).tab[tidx g ir ir2 d]!.1 == 1) = true := hsc
      rw [hd, tab_entry g dtl hir hir2 hit hit2] at hs
      simp only [prepE] at hs
      rw [entryF_fst, hrg ir hir, hrg ir2 hir2] at hs
      by_contra hc
      rw [if_neg hc] at hs
      split_ifs at hs <;> simp at hs
    -- polar coordinates of the two points
    rw [cell_eq_sector] at hw hz
    obtain ⟨⟨ρ, φ⟩, ⟨hρ, hφ⟩, rfl⟩ := hw
    obtain ⟨⟨ρ', φ'⟩, ⟨hρ', hφ'⟩, rfl⟩ := hz
    simp only [mem_Ioo] at hρ hφ hρ' hφ'
    rw [polarCoord_symm_apply, polarCoord_symm_apply, sqDist_add_zero, enorm2_polar_add_sq]
    -- the angle between them
    have hang : ∀ i : ℕ, (gR g).ang i = -(π / 2) + i * h := by
      intro i; show GridR.ang ⟨g.N1, g.N2, g.NT⟩ i = _; unfold GridR.ang; simp only; rw [hh_def]; ring
    have hNh : h * g.NT = π := by rw [hh_def]; field_simp
    rw [hang, hang] at hφ; rw [hang, hang] at hφ'
    push_cast at hφ hφ'
    have hcos := hAR h d g.NT hh hNh hdlt (φ - (gR g).ang it) (φ' - (gR g).ang it)
      (by rw [hang]; linarith) (by rw [hang]; linarith)
      (by rw [hang, hdr]; linarith) (by rw [hang, hdr]; linarith)
    have esub : φ' - (gR g).ang it - (φ - (gR g).ang it) = φ' - φ := by ring
    rw [esub] at hcos
    -- enclosures
    obtain ⟨hr1, hr2, -⟩ := hRing ir hir
    obtain ⟨hq1, hq2, -⟩ := hRing ir2 hir2
    obtain ⟨-, -, hdd⟩ := hAS g hNT hNTb
    obtain ⟨-, -, hcmin, hcmax⟩ := hdd d hdlt
    have hc2 : (if |d| ≤ 1 then (1 : ℝ) else Real.cos ((|d| - 1) * (π / g.NT))) ≤ 1 := by
      split_ifs
      · exact le_refl 1
      · exact Real.cos_le_one _
    have hfr := hFR (mkRing g ir).r1 (mkRing g ir).r2 (mkRing g ir2).r1 (mkRing g ir2).r2 (mkDData g d).cmin
      (mkDData g d).cmax ((gR g).rad ir) ((gR g).rad (ir + 1)) ((gR g).rad ir2) ((gR g).rad (ir2 + 1))
      (Real.cos ((|d| + 1) * (π / g.NT))) (if |d| ≤ 1 then 1 else Real.cos ((|d| - 1) * (π / g.NT)))
      hr1 hr2 hq1 hq2 hcmin hcmax ((gR g).rad_nonneg ir) ((gR g).rad_nonneg ir2) (Real.neg_one_le_cos _) hc2
      ρ ρ' (Real.cos (φ' - φ)) hρ.1.le hρ.2.le hρ'.1.le hρ'.2.le hcos.1 hcos.2
    have hONE : fx ONE = 1 := by unfold fx ONE PR; norm_num
    have h3 := fx_le_iff.mpr hfmax
    rw [hONE] at h3
    linarith [hfr.2]
  · -- nf
    intro ir it hir hit hnf z hz
    rw [hNR] at hir
    obtain ⟨-, -, -, -, -, -, -, hfl⟩ := hRing ir hir
    unfold discOf at hnf; simp only at hnf
    rw [rings_get g dtl hir] at hnf
    have hr1 := hfl hnf
    rw [cell_eq_sector] at hz
    obtain ⟨⟨ρ, φ⟩, ⟨hρ, hφ⟩, rfl⟩ := hz
    simp only [mem_Ioo] at hρ
    have hρ0 : 0 ≤ ρ := le_trans ((gR g).rad_nonneg ir) hρ.1.le
    rw [polarCoord_symm_apply]
    unfold sqDist; simp only [Prod.fst_zero, Prod.snd_zero, sub_zero]
    have : (ρ * Real.cos φ) ^ 2 + (ρ * Real.sin φ) ^ 2 = ρ ^ 2 := by
      linear_combination ρ ^ 2 * Real.cos_sq_add_sin_sq φ
    rw [this]
    nlinarith

end BHH.W2.TSO
