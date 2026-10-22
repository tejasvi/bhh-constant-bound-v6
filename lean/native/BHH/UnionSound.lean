/-
Module B of the box part: soundness of the union-area enclosure `BHH.Cert.unionArea` (BHHCert/Union.lean).

* `US.unionArea_spec`: if `unionArea cs pts R cand = some u` (`cs` sound, `R > 0`, any candidate source `cand`), the
  centres are distinct, `u.A` encloses `Σ_i ∫_{E_i} (ρ² + ρ⟨c_i, u(t)⟩)/2 dt` and `u.gx`, `u.gy` enclose
  `∫_{E_i} cos`, `∫_{E_i} sin`, where `ρ = R / 2^PR` and `E_i ⊆ [0, 2π)` are the directions `t` with `c_i + ρ u(t)`
  outside every open disk `B°(c_j, ρ)`, `j ≠ i`.
* `greenSound`: radius 1, enclosures of `greenArea` (right-hand side of (2.1)) and `greenGrad`, no hypothesis.
* `unionSound : UnionSoundProp` (radius 1, with Green's formula (2.1) for the area and the gradient formula as the
  definition `greenGrad`), `unionSoundR : UnionSoundRProp` (radius `R`, by scaling to radius 1).
-/
import BHH.UnionSound.Pairs

open BHH.Cert Real Set MeasureTheory
open scoped Pointwise

namespace BHH

noncomputable section

namespace US

/-! ## real centres and covered directions -/

/-- the real centre of point `k` (`(0, 0)` beyond the list) -/
def cR (pts : List (ℤ × ℤ)) (k : ℕ) : Pt := (fx (pts.getD k (0, 0)).1, fx (pts.getD k (0, 0)).2)

lemma ptsCfg_eq (pts : List (ℤ × ℤ)) (i : Fin pts.length) : ptsCfg pts.length pts i = cR pts i.val := rfl

/-- the directions of circle `k` (radius `ρ`) that lie in the open disk around point `l` -/
def Cov (ρ : ℝ) (pts : List (ℤ × ℤ)) (k l : ℕ) : Set ℝ :=
  {t | ¬ (ρ ^ 2 ≤ sqDist (cR pts k + ρ • dir t) (cR pts l))}

/-- the exposed directions of circle `i` for the union of the disks `B(y_j, ρ)` -/
def expR {k : ℕ} (y : Fin k → Pt) (ρ : ℝ) (i : Fin k) : Set ℝ :=
  {t | t ∈ Ico 0 (2 * π) ∧ ∀ j, j ≠ i → ρ ^ 2 ≤ sqDist (y i + ρ • dir t) (y j)}

lemma sqDist_shift (c c' : Pt) (ρ t : ℝ) :
    sqDist (c + ρ • dir t) c' =
      ρ ^ 2 - Gf ρ (c'.1 - c.1) (c'.2 - c.2) ((c'.1 - c.1) ^ 2 + (c'.2 - c.2) ^ 2) t := by
  simp only [sqDist, dir, Gf, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  linear_combination ρ ^ 2 * Real.sin_sq_add_cos_sq t

lemma cR_sub_fst (pts : List (ℤ × ℤ)) (k l : ℕ) : (cR pts l).1 - (cR pts k).1 = fx (wxOf pts k l) := by
  simp [cR, wxOf, fx_sub]

lemma cR_sub_snd (pts : List (ℤ × ℤ)) (k l : ℕ) : (cR pts l).2 - (cR pts k).2 = fx (wyOf pts k l) := by
  simp [cR, wyOf, fx_sub]

lemma Cov_eq (ρ : ℝ) (pts : List (ℤ × ℤ)) (k l : ℕ) : Cov ρ pts k l =
    {t | 0 < Gf ρ (fx (wxOf pts k l)) (fx (wyOf pts k l)) (fx (wxOf pts k l) ^ 2 + fx (wyOf pts k l) ^ 2) t} := by
  ext t
  simp only [Cov, Set.mem_setOf_eq, sqDist_shift, cR_sub_fst, cR_sub_snd, not_le]
  constructor <;> intro h <;> linarith

lemma wxOf_swap (pts : List (ℤ × ℤ)) (k l : ℕ) : wxOf pts l k = -wxOf pts k l := by simp [wxOf]
lemma wyOf_swap (pts : List (ℤ × ℤ)) (k l : ℕ) : wyOf pts l k = -wyOf pts k l := by simp [wyOf]
lemma d2Of_swap (pts : List (ℤ × ℤ)) (k l : ℕ) : d2Of pts l k = d2Of pts k l := by
  unfold d2Of; rw [wxOf_swap pts k l, wyOf_swap pts k l]; ring

lemma fx_sq_add (a b : ℤ) : fx a ^ 2 + fx b ^ 2 = ((a * a + b * b : ℤ) : ℝ) / SC ^ 2 := by
  simp only [fx_eq]; push_cast; field_simp

lemma d_pos_of_ne {pts : List (ℤ × ℤ)} {k l : ℕ} (h : d2Of pts k l ≠ 0) :
    0 < fx (wxOf pts k l) ^ 2 + fx (wyOf pts k l) ^ 2 := by
  rw [fx_sq_add]
  apply div_pos _ (by have := SC_pos; positivity)
  have h0 : 0 ≤ wxOf pts k l * wxOf pts k l + wyOf pts k l * wyOf pts k l := by nlinarith
  have : 0 < wxOf pts k l * wxOf pts k l + wyOf pts k l * wyOf pts k l := lt_of_le_of_ne h0 (Ne.symm h)
  exact_mod_cast this

lemma cR_ne_of_d2 {pts : List (ℤ × ℤ)} {k l : ℕ} (h : d2Of pts k l ≠ 0) : cR pts k ≠ cR pts l := by
  intro he
  have h1 := cR_sub_fst pts k l
  have h2 := cR_sub_snd pts k l
  rw [he, sub_self] at h1 h2
  have := d_pos_of_ne h
  rw [← h1, ← h2] at this
  simp at this

/-- far disks cover nothing -/
lemma not_mem_Cov_of_far {pts : List (ℤ × ℤ)} {R : ℤ} (hR : 0 ≤ R) {k l : ℕ} (h : 4 * R * R ≤ d2Of pts k l)
    (t : ℝ) : t ∉ Cov (fx R) pts k l := by
  rw [Cov_eq]
  simp only [Set.mem_setOf_eq, not_lt]
  set wx := fx (wxOf pts k l)
  set wy := fx (wyOf pts k l)
  set ρ := fx R
  have hρ : 0 ≤ ρ := fx_nonneg_iff.mpr hR
  have h4 : 4 * ρ ^ 2 ≤ wx ^ 2 + wy ^ 2 := by
    rw [fx_sq_add]
    have hS := SC_pos
    have : ((4 * R * R : ℤ) : ℝ) ≤ ((d2Of pts k l : ℤ) : ℝ) := by exact_mod_cast h
    simp only [d2Of] at this
    rw [le_div_iff₀ (by positivity)]
    have e : 4 * ρ ^ 2 * SC ^ 2 = ((4 * R * R : ℤ) : ℝ) := by
      simp only [ρ, fx_eq]; push_cast; field_simp
    rw [e]; exact this
  have hcs : (wx * Real.cos t + wy * Real.sin t) ^ 2 ≤ wx ^ 2 + wy ^ 2 := by
    have := Real.sin_sq_add_cos_sq t
    nlinarith [sq_nonneg (wx * Real.sin t - wy * Real.cos t)]
  unfold Gf
  set X := wx * Real.cos t + wy * Real.sin t
  rcases le_or_gt X 0 with hX | hX
  · nlinarith [sq_nonneg wx, sq_nonneg wy]
  · nlinarith [mul_le_mul_of_nonneg_left hcs (by positivity : (0 : ℝ) ≤ 4 * ρ ^ 2),
      mul_le_mul_of_nonneg_right h4 (by positivity : (0 : ℝ) ≤ wx ^ 2 + wy ^ 2)]

/-- the arcs of a recorded pair are proxies of the covered sets on both circles -/
lemma arcFor_pair (cs : ℤ → Iv × Iv) (hcs : CosSinSound cs) (pts : List (ℤ × ℤ)) {R : ℤ} (hR : 0 ≤ R)
    {cand : CandFn} {a b : ℕ} {ar : Arc} (hd : d2Of pts a b ≠ 0)
    (hc : certArc cs (wxOf pts a b) (wyOf pts a b) (d2Of pts a b) R cand = some ar) :
    ArcFor (Cov (fx R) pts a b) ar ∧ ArcFor (Cov (fx R) pts b a) (shiftArc ar) := by
  have hcert := certArc_spec cs hcs hR rfl hc
  have hd0 := d_pos_of_ne hd
  constructor
  · rw [Cov_eq]; exact arcFor_of_cert hd0 hcert
  · have h := arcFor_shift_of_cert hd0 hcert
    have hset : Cov (fx R) pts b a = {t | 0 < Gf (fx R) (fx (wxOf pts a b)) (fx (wyOf pts a b))
        (fx (wxOf pts a b) ^ 2 + fx (wyOf pts a b) ^ 2) (t - π)} := by
      rw [Cov_eq, wxOf_swap pts a b, wyOf_swap pts a b, fx_neg, fx_neg, neg_sq, neg_sq]
      ext t
      simp only [Set.mem_setOf_eq, Gf_sub_pi]
    rw [hset]; exact h

/-- the exposed set of circle `i` is `[0, 2π)` minus the covered sets of its arcs -/
lemma expSet_eq {cs : ℤ → Iv × Iv} {pts : List (ℤ × ℤ)} {R : ℤ} (hR : 0 ≤ R) {cand : CandFn}
    {pa : List (ℕ × ℕ × Arc)} (hpa : pairArcs cs pts R cand = some pa) (i : Fin pts.length) :
    expSet (arcsOfS (Cov (fx R) pts) pa i.val) = expR (ptsCfg pts.length pts) (fx R) i := by
  obtain ⟨hdist, hrec, hall⟩ := pairArcs_spec hpa
  ext t
  constructor
  · rintro ⟨htI, hL⟩
    refine ⟨htI, fun j hji => ?_⟩
    by_contra hcon
    rw [ptsCfg_eq, ptsCfg_eq] at hcon
    have htC : t ∈ Cov (fx R) pts i.val j.val := hcon
    have hne : j.val ≠ i.val := fun h => hji (Fin.ext h)
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · by_cases hfar : 4 * R * R ≤ d2Of pts j.val i.val
      · rw [d2Of_swap] at hfar
        exact not_mem_Cov_of_far hR hfar t htC
      · obtain ⟨ar, har⟩ := hall j.val i.val hlt i.isLt hfar
        exact hL _ (arcsOfS_mem_snd (x := (j.val, i.val, ar)) har (by simpa using hne) rfl) htC
    · by_cases hfar : 4 * R * R ≤ d2Of pts i.val j.val
      · exact not_mem_Cov_of_far hR hfar t htC
      · obtain ⟨ar, har⟩ := hall i.val j.val hgt j.isLt hfar
        exact hL _ (arcsOfS_mem_fst (x := (i.val, j.val, ar)) har rfl) htC
  · rintro ⟨htI, hE⟩
    refine ⟨htI, fun q hq htq => ?_⟩
    obtain ⟨x, hx, hq'⟩ := mem_arcsOfS hq
    obtain ⟨hlt, hlen, -, -⟩ := hrec x hx
    rcases hq' with ⟨hx1, rfl⟩ | ⟨-, hx2, rfl⟩
    · have hj : x.2.1 ≠ i.val := by omega
      have := hE ⟨x.2.1, hlen⟩ (fun h => hj (congrArg Fin.val h))
      rw [ptsCfg_eq, ptsCfg_eq] at this
      simp only at this
      rw [← hx1] at this
      exact htq this
    · have hj : x.1 ≠ i.val := by omega
      have := hE ⟨x.1, by omega⟩ (fun h => hj (congrArg Fin.val h))
      rw [ptsCfg_eq, ptsCfg_eq] at this
      simp only at this
      rw [← hx2] at this
      exact htq this

/-! ## the result list -/

lemma res_length {β γ : Type*} (l : List β) (f : ℕ × β → γ) :
    (((List.range l.length).zip l).map f).length = l.length := by simp

lemma res_getElem {β γ : Type*} (l : List β) (f : ℕ × β → γ) (k : ℕ) (hk : k < l.length) :
    (((List.range l.length).zip l).map f)[k]'(by simpa using hk) = f (k, l[k]) := by
  simp [List.getElem_map, List.getElem_zip, List.getElem_range]

lemma foldl_add_spec : ∀ (l : List (Iv × Iv × Iv)) (v : ℕ → ℝ) (x0 : ℝ) (a0 : Iv), ivMem x0 a0 →
    (∀ k (hk : k < l.length), ivMem (v k) (l[k]).1) →
    ivMem (x0 + ∑ k ∈ Finset.range l.length, v k) (l.foldl (fun acc r => Iv.add acc r.1) a0)
  | [], v, x0, a0, h0, _ => by simpa using h0
  | r :: l, v, x0, a0, h0, h => by
    simp only [List.foldl_cons, List.length_cons]
    have h1 := foldl_add_spec l (fun k => v (k + 1)) (x0 + v 0) (Iv.add a0 r.1)
      (Iv.mem_add h0 (h 0 (by simp))) (fun k hk => h (k + 1) (by simp; omega))
    rw [Finset.sum_range_succ']
    convert h1 using 1
    ring

/-! ## the main enclosure -/

/-- Soundness of `unionArea` for radius `R / 2^PR`, any candidate source. -/
theorem unionArea_spec (cs : ℤ → Iv × Iv) (hcs : CosSinSound cs) (cand : CandFn) (pts : List (ℤ × ℤ)) (R : ℤ)
    (hR : 0 < R) (u : UnionRes) (h : BHH.Cert.unionArea cs pts R cand = some u) :
    (∀ i j : Fin pts.length, i ≠ j → ptsCfg pts.length pts i ≠ ptsCfg pts.length pts j) ∧
    ivMem (∑ i : Fin pts.length,
      ∫ t in expR (ptsCfg pts.length pts) (fx R) i,
        fA (fx R) (ptsCfg pts.length pts i).1 (ptsCfg pts.length pts i).2 t) u.A ∧
    ∀ i : Fin pts.length,
      ivMem (∫ t in expR (ptsCfg pts.length pts) (fx R) i, Real.cos t) (u.gx.getD i.val default) ∧
      ivMem (∫ t in expR (ptsCfg pts.length pts) (fx R) i, Real.sin t) (u.gy.getD i.val default) := by
  unfold BHH.Cert.unionArea at h
  rcases hpa : pairArcs cs pts R cand with _ | pa
  · rw [hpa] at h; exact absurd h (by simp)
  rw [hpa] at h
  simp only [Option.some.injEq] at h
  subst h
  obtain ⟨hdist, hrec, hall⟩ := pairArcs_spec hpa
  -- the arcs of circle `i` are proxies of its covered sets
  have hL : ∀ i : ℕ, ∀ q ∈ arcsOfS (Cov (fx R) pts) pa i, ArcFor q.2 q.1 := by
    intro i q hq
    obtain ⟨x, hx, hq'⟩ := mem_arcsOfS hq
    obtain ⟨hlt, hlen, -, hc⟩ := hrec x hx
    have hd := hdist x.1 x.2.1 hlt hlen
    obtain ⟨h1, h2⟩ := arcFor_pair cs hcs pts hR.le hd hc
    rcases hq' with ⟨-, rfl⟩ | ⟨-, -, rfl⟩
    · exact h1
    · exact h2
  -- one circle
  have hcirc : ∀ i : Fin pts.length,
      ivMem (∫ t in expR (ptsCfg pts.length pts) (fx R) i,
          fA (fx R) (ptsCfg pts.length pts i).1 (ptsCfg pts.length pts i).2 t)
        (circleInt R (pts[i.val]).1 (pts[i.val]).2 (arcsOf pa i.val)).1 ∧
      ivMem (∫ t in expR (ptsCfg pts.length pts) (fx R) i, Real.cos t)
        (circleInt R (pts[i.val]).1 (pts[i.val]).2 (arcsOf pa i.val)).2.1 ∧
      ivMem (∫ t in expR (ptsCfg pts.length pts) (fx R) i, Real.sin t)
        (circleInt R (pts[i.val]).1 (pts[i.val]).2 (arcsOf pa i.val)).2.2 := by
    intro i
    have hc := circleInt_spec R (pts[i.val]).1 (pts[i.val]).2 hR.le _ (hL i.val)
    rw [arcsOfS_map, expSet_eq hR.le hpa i] at hc
    have hp : ptsCfg pts.length pts i = (fx (pts[i.val]).1, fx (pts[i.val]).2) := by
      simp only [ptsCfg, List.getD_eq_getElem _ _ i.isLt]
    rw [hp]
    exact hc
  refine ⟨?_, ?_, ?_⟩
  · intro i j hij
    rw [ptsCfg_eq, ptsCfg_eq]
    have hne : i.val ≠ j.val := fun h => hij (Fin.ext h)
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact cR_ne_of_d2 (hdist _ _ hlt j.isLt)
    · exact fun he => cR_ne_of_d2 (hdist _ _ hgt i.isLt) he.symm
  · -- the area: the sum over the circles
    simp only
    set v : ℕ → ℝ := fun k => if hk : k < pts.length then
      ∫ t in expR (ptsCfg pts.length pts) (fx R) ⟨k, hk⟩,
        fA (fx R) (ptsCfg pts.length pts ⟨k, hk⟩).1 (ptsCfg pts.length pts ⟨k, hk⟩).2 t else 0
      with hv
    have hsum : ∑ i : Fin pts.length,
        ∫ t in expR (ptsCfg pts.length pts) (fx R) i,
          fA (fx R) (ptsCfg pts.length pts i).1 (ptsCfg pts.length pts i).2 t
        = ∑ k ∈ Finset.range pts.length, v k := by
      rw [← Fin.sum_univ_eq_sum_range]
      apply Finset.sum_congr rfl
      intro i _
      simp [hv, i.isLt]
    rw [hsum]
    have key := foldl_add_spec (((List.range pts.length).zip pts).map fun x =>
        circleInt R x.2.1 x.2.2 (arcsOf pa x.1)) v 0 (Iv.int 0) (by simpa using Iv.mem_int 0) (by
      intro k hk
      rw [res_length] at hk
      rw [res_getElem pts _ k hk]
      simp only [hv, hk, dite_true]
      exact (hcirc ⟨k, hk⟩).1)
    rw [res_length, zero_add] at key
    exact key
  · intro i
    have hi : i.val < (((List.range pts.length).zip pts).map fun x =>
        circleInt R x.2.1 x.2.2 (arcsOf pa x.1)).length := by rw [res_length]; exact i.isLt
    have e1 : ((((List.range pts.length).zip pts).map fun x =>
        circleInt R x.2.1 x.2.2 (arcsOf pa x.1)).map (·.2.1)).getD i.val default
        = (circleInt R (pts[i.val]).1 (pts[i.val]).2 (arcsOf pa i.val)).2.1 := by
      rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map, res_getElem pts _ i.val i.isLt]
    have e2 : ((((List.range pts.length).zip pts).map fun x =>
        circleInt R x.2.1 x.2.2 (arcsOf pa x.1)).map (·.2.2)).getD i.val default
        = (circleInt R (pts[i.val]).1 (pts[i.val]).2 (arcsOf pa i.val)).2.2 := by
      rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map, res_getElem pts _ i.val i.isLt]
    simp only
    rw [e1, e2]
    exact ⟨(hcirc i).2.1, (hcirc i).2.2⟩

end US

/-! ## the interface Props -/

open US in
/-- Module B without Green's formula, unit radius: if `unionArea` succeeds, the centres are distinct and `u` encloses
the right-hand side `greenArea` of (2.1) and the gradient formula `greenGrad` at every centre. -/
theorem greenSound : ∀ (cs : ℤ → Iv × Iv), CosSinSound cs → ∀ (cand : CandFn) (k : ℕ) (pts : List (ℤ × ℤ))
    (u : UnionRes), pts.length = k → BHH.Cert.unionArea cs pts ONE cand = some u →
      (∀ i j : Fin k, i ≠ j → ptsCfg k pts i ≠ ptsCfg k pts j) ∧
      ivMem (greenArea (ptsCfg k pts)) u.A ∧
      ∀ i : Fin k,
        ivMem (greenGrad (ptsCfg k pts) i).1 (u.gx.getD i.val default) ∧
        ivMem (greenGrad (ptsCfg k pts) i).2 (u.gy.getD i.val default) := by
  intro cs hcs cand k pts u hk h
  subst hk
  obtain ⟨hdist, hA, hgrad⟩ := unionArea_spec cs hcs cand pts ONE (by norm_num [ONE]) u h
  have hρ : fx ONE = 1 := by rw [fx_eq, ONE_cast]; exact div_self SC_pos.ne'
  rw [hρ] at hA hgrad
  have hexp : ∀ i, expR (ptsCfg pts.length pts) 1 i = exposed (ptsCfg pts.length pts) i := by
    intro i; ext t; simp [expR, exposed]
  refine ⟨hdist, ?_, ?_⟩
  · unfold greenArea
    convert hA using 1
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [hexp i, ← integral_const_mul]
    congr 1
    funext t
    simp only [fA]
    ring
  · intro i
    have := hgrad i
    rw [hexp i] at this
    exact this

/-- Module B, unit radius: `UnionSoundProp`. -/
theorem unionSound : UnionSoundProp := by
  intro hG cs hcs cand k pts u hk h
  obtain ⟨hdist, hA, hgrad⟩ := greenSound cs hcs cand k pts u hk h
  rw [hG k (ptsCfg k pts) hdist]
  exact ⟨hA, hgrad⟩

open US in
/-- Module B, radius `R`: `UnionSoundRProp` (Green's formula after scaling to radius 1). -/
theorem unionSoundR : UnionSoundRProp := by
  intro hG cs hcs cand k pts R u hk hR h
  subst hk
  obtain ⟨hdist, hA, -⟩ := unionArea_spec cs hcs cand pts R hR u h
  set ρ := fx R with hρdef
  have hρ : 0 < ρ := fx_pos_iff.mpr hR
  set y := ptsCfg pts.length pts with hy
  set z : Fin pts.length → Pt := fun i => ρ⁻¹ • y i with hz
  have hsq : ∀ a b : Pt, sqDist (ρ⁻¹ • a) (ρ⁻¹ • b) = ρ⁻¹ ^ 2 * sqDist a b := by
    intro a b
    simp only [sqDist, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    ring
  have hzdist : ∀ i j, i ≠ j → z i ≠ z j := by
    intro i j hij he
    apply hdist i j hij
    have := congrArg (fun w : Pt => ρ • w) he
    simpa [hz, smul_smul, hρ.ne'] using this
  -- scaling of the union
  have hset : (⋃ i, disk (y i) ρ) = ρ • ⋃ i, disk (z i) 1 := by
    ext w
    rw [Set.mem_smul_set_iff_inv_smul_mem₀ hρ.ne', mem_iUnion, mem_iUnion]
    apply exists_congr
    intro i
    simp only [disk, Set.mem_setOf_eq, hz, hsq, one_pow]
    rw [inv_pow, inv_mul_le_iff₀ (by positivity), mul_one]
  have hscale : (volume (⋃ i, disk (y i) ρ)).toReal = ρ ^ 2 * unionArea z := by
    rw [hset, Measure.addHaar_smul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (abs_nonneg _)]
    unfold unionArea
    congr 1
    rw [show Module.finrank ℝ (ℝ × ℝ) = 2 by simp, abs_of_nonneg (by positivity)]
  have hexp : ∀ i, exposed z i = expR y ρ i := by
    intro i
    ext t
    simp only [exposed, expR, Set.mem_setOf_eq]
    apply and_congr_right
    intro _
    apply forall_congr'
    intro j
    apply imp_congr_right
    intro _
    have e : z i + dir t = ρ⁻¹ • (y i + ρ • dir t) := by
      simp only [hz, smul_add, smul_smul, inv_mul_cancel₀ hρ.ne', one_smul]
    rw [e, show z j = ρ⁻¹ • y j from rfl, hsq, inv_pow, le_inv_mul_iff₀ (by positivity), mul_one]
  rw [hscale, hG _ z hzdist]
  unfold greenArea
  convert hA using 1
  rw [← mul_assoc, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [hexp i, ← integral_const_mul]
  congr 1
  funext t
  simp only [fA, hz, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  field_simp
  ring

end

end BHH
