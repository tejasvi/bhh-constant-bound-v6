/-
T4 (`DistSound`): `distHi` bounds the distance from an interval point to an exact point; `epsCell` bounds the
distance from the centroid to the points of a sector (`|z - c|² = ρ² + R² - 2ρR cos(φ - m) ≤ ρ² + R² - 2ρR cos(h/2)`,
a quadratic in `ρ`, at most its larger end value); `vertexDistHi` bounds the distances from the two vertices of the
unit circles around `a`, `b` to `l` (when the rounded `|b - a|` has a positive lower end).
-/
import W2.TabIvl
import W2.GeoQuad
import W2.GeoProps

open Set Real BHH.Cert

noncomputable section

namespace BHH.W2.TabB

open BHH BHH.W2 W2C

lemma edist2_eq (a b : Pt) : edist2 a b = √((a.1 - b.1) ^ 2 + (a.2 - b.2) ^ 2) := rfl

/-- the distance bound of an interval point `(px, py)` to an exact point -/
lemma mem_distIv {x y : ℝ} {px py : Iv} (hx : ivMem x px) (hy : ivMem y py) (qx qy : ℤ) :
    ivMem (edist2 (x, y) (fx qx, fx qy))
      (Iv.sqrt (Iv.add (Iv.sqr (Iv.sub px (Iv.pt qx))) (Iv.sqr (Iv.sub py (Iv.pt qy))))) := by
  rw [edist2_eq]
  exact Iv.mem_sqrt (Iv.mem_add (Iv.mem_sqr (Iv.mem_sub hx (Iv.mem_pt qx))) (Iv.mem_sqr (Iv.mem_sub hy (Iv.mem_pt qy))))

/-- T4 (a) -/
theorem distHi_sound (px py : Iv) (qx qy : ℤ) (x y : ℝ) (hx : ivMem x px) (hy : ivMem y py) :
    edist2 (x, y) (fx qx, fx qy) ≤ fx (distHi px py qx qy) :=
  ivMem_hi_le (mem_distIv hx hy qx qy)

lemma secRho_nonneg {r1 r2 h : ℝ} (hr1 : 0 ≤ r1) (hr12 : r1 < r2) (hh0 : 0 < h) (hh1 : h ≤ π) :
    0 ≤ secRho r1 r2 0 h := by
  unfold secRho
  have h2 : 0 < r2 := lt_of_le_of_lt hr1 hr12
  have hn : 0 ≤ r2 ^ 3 - r1 ^ 3 := by
    have := pow_le_pow_left₀ hr1 hr12.le 3
    linarith
  have hd : 0 < r2 ^ 2 - r1 ^ 2 := by nlinarith
  have hs : 0 ≤ Real.sin ((h - 0) / 2) := Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
  have hh : 0 < (h - 0) / 2 := by linarith
  positivity

lemma secRho_shift (r1 r2 a h : ℝ) : secRho r1 r2 a (a + h) = secRho r1 r2 0 h := by
  unfold secRho
  rw [show a + h - a = h - 0 by ring]

/-- T4 (b) -/
theorem epsCell_sound (R : Ring) (ch : Iv) (r1 r2 a h : ℝ) (hr1 : ivMem r1 R.r1) (hr2 : ivMem r2 R.r2)
    (hrho : ivMem (secRho r1 r2 0 h) R.rhoc) (hch : ivMem (Real.cos (h / 2)) ch) (h0 : 0 ≤ r1) (h12 : r1 < r2)
    (hh0 : 0 < h) (hh1 : h ≤ π / 2) (_ha : -π ≤ a) (_hah : a + h ≤ π) :
    ∀ z ∈ sector r1 r2 a (a + h), edist2 z (secCentroid r1 r2 a (a + h)) ≤ fx (epsCell R ch) := by
  intro z hz
  obtain ⟨⟨ρ, φ⟩, hmem, rfl⟩ := hz
  simp only [mem_prod, mem_Ioo] at hmem
  obtain ⟨⟨hρ1, hρ2⟩, hφ1, hφ2⟩ := hmem
  have hpi := pi_pos
  set R0 := secRho r1 r2 0 h with hR0
  have hR0n : 0 ≤ R0 := secRho_nonneg h0 h12 hh0 (by linarith)
  set m := (a + (a + h)) / 2 with hm
  set c := Real.cos (h / 2) with hc
  have hρ0 : 0 ≤ ρ := by linarith
  -- the squared distance
  have hdist : edist2 (polarCoord.symm (ρ, φ)) (secCentroid r1 r2 a (a + h)) =
      √(ρ ^ 2 + R0 ^ 2 - 2 * ρ * R0 * Real.cos (φ - m)) := by
    rw [edist2_eq, secCentroid, secRho_shift, polarCoord_symm_apply]
    congr 1
    simp only
    rw [Real.cos_sub]
    have h1 := Real.cos_sq_add_sin_sq φ
    have h2 := Real.cos_sq_add_sin_sq m
    rw [← hm, ← hR0]
    nlinarith [h1, h2]
  have hcos : c ≤ Real.cos (φ - m) := by
    rw [hc, ← Real.cos_abs (φ - m)]
    exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith)
      (abs_le.mpr ⟨by rw [hm]; linarith, by rw [hm]; linarith⟩)
  -- the quadratic `G ρ = ρ² - 2 R0 c ρ + R0²`
  have hG : ρ ^ 2 + R0 ^ 2 - 2 * ρ * R0 * Real.cos (φ - m) ≤ ρ ^ 2 + (-(2 * R0 * c)) * ρ + R0 ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hcos (mul_nonneg hρ0 hR0n)]
  have hq := quad_le_max (β := -(2 * R0 * c)) (γ := R0 ^ 2) hρ1.le hρ2.le
  -- the interval values at the two radii
  have hf : ∀ (r : ℝ) (I : Iv), ivMem r I →
      r ^ 2 + (-(2 * R0 * c)) * r + R0 ^ 2 ≤
        fx (Iv.add (Iv.sqr I) (Iv.sub (Iv.sqr R.rhoc) (Iv.mul2e (Iv.mul (Iv.mul I R.rhoc) ch) 1))).hi := by
    intro r I hI
    have := ivMem_hi_le (Iv.mem_add (Iv.mem_sqr hI)
      (Iv.mem_sub (Iv.mem_sqr hrho) (Iv.mem_mul2e (Iv.mem_mul (Iv.mem_mul hI hrho) hch) 1)))
    linarith
  have hf1 := hf r1 R.r1 hr1
  have hf2 := hf r2 R.r2 hr2
  unfold epsCell
  dsimp only
  set M := max (max (Iv.add (Iv.sqr R.r1) (Iv.sub (Iv.sqr R.rhoc) (Iv.mul2e (Iv.mul (Iv.mul R.r1 R.rhoc) ch) 1))).hi
    (Iv.add (Iv.sqr R.r2) (Iv.sub (Iv.sqr R.rhoc) (Iv.mul2e (Iv.mul (Iv.mul R.r2 R.rhoc) ch) 1))).hi) 0 with hM
  have hsq : ρ ^ 2 + R0 ^ 2 - 2 * ρ * R0 * Real.cos (φ - m) ≤ fx M := by
    refine hG.trans (hq.trans ?_)
    rw [hM, fx_max, fx_max]
    exact le_max_of_le_left (max_le_max hf1 hf2)
  have hroot := ivMem_hi_le (Iv.mem_sqrt (Iv.mem_pt M))
  rw [hdist]
  have h1 : fx (Iv.sqrt (Iv.pt M)).hi ≤ fx ((Iv.sqrt ⟨M, M⟩).hi + 1) := fx_le_iff.mpr (by unfold Iv.pt; omega)
  exact (Real.sqrt_le_sqrt hsq).trans (hroot.trans h1)

/-- the rounded `|b - a|` of `vertexDistHi` -/
def vertexDc (ax ay bx by_ : ℤ) : Iv :=
  Iv.sqrt (Iv.add (Iv.sqr (Iv.pt (bx - ax))) (Iv.sqr (Iv.pt (by_ - ay))))

lemma fx_sub (a b : ℤ) : fx (a - b) = fx a - fx b := by unfold fx; push_cast; ring

/-- T4 (c), when the rounded `|b - a|` has a positive lower end -/
theorem vertexDistHi_sound (ax ay bx by_ lx ly : ℤ) (hdc : 0 < (vertexDc ax ay bx by_).lo) :
    edist2 (vertexPts (fx ax, fx ay) (fx bx, fx by_)).1 (fx lx, fx ly) ≤ fx (vertexDistHi ax ay bx by_ lx ly).1 ∧
      edist2 (vertexPts (fx ax, fx ay) (fx bx, fx by_)).2 (fx lx, fx ly) ≤
        fx (vertexDistHi ax ay bx by_ lx ly).2 := by
  set wx := bx - ax with hwx
  set wy := by_ - ay with hwy
  set Q := fx wx ^ 2 + fx wy ^ 2 with hQ
  have hQ0 : 0 ≤ Q := by positivity
  have hd2 : ivMem Q (Iv.add (Iv.sqr (Iv.pt wx)) (Iv.sqr (Iv.pt wy))) :=
    Iv.mem_add (Iv.mem_sqr (Iv.mem_pt wx)) (Iv.mem_sqr (Iv.mem_pt wy))
  have hdcm : ivMem (√Q) (vertexDc ax ay bx by_) := Iv.mem_sqrt hd2
  have hsm : ivMem (√(1 - Q / 2 ^ 2) / √Q) (Iv.div (Iv.sqrt (Iv.sub (Iv.int 1) (Iv.div2e (Iv.add
      (Iv.sqr (Iv.pt wx)) (Iv.sqr (Iv.pt wy))) 2))) (vertexDc ax ay bx by_)) := by
    have h1 := Iv.mem_sqrt (Iv.mem_sub (Iv.mem_int 1) (Iv.mem_div2e hd2 2))
    rw [Int.cast_one] at h1
    exact Iv.mem_div h1 hdcm hdc
  have hmx : ivMem (fx ax + fx wx / 2 ^ 1) (Iv.add (Iv.pt ax) (Iv.div2e (Iv.pt wx) 1)) :=
    Iv.mem_add (Iv.mem_pt ax) (Iv.mem_div2e (Iv.mem_pt wx) 1)
  have hmy : ivMem (fx ay + fx wy / 2 ^ 1) (Iv.add (Iv.pt ay) (Iv.div2e (Iv.pt wy) 1)) :=
    Iv.mem_add (Iv.mem_pt ay) (Iv.mem_div2e (Iv.mem_pt wy) 1)
  have hox := Iv.mem_mul hsm (Iv.mem_pt (-wy))
  have hoy := Iv.mem_mul hsm (Iv.mem_pt wx)
  have hw1 : fx bx - fx ax = fx wx := by rw [hwx, fx_sub]
  have hw2 : fx by_ - fx ay = fx wy := by rw [hwy, fx_sub]
  have hen : enorm2 ((fx bx, fx by_) - (fx ax, fx ay)) = √Q := by
    unfold enorm2
    simp only [Prod.fst_sub, Prod.snd_sub]
    rw [hw1, hw2]
  have hss : √(1 - √Q ^ 2 / 4) / √Q = √(1 - Q / 2 ^ 2) / √Q := by
    rw [Real.sq_sqrt hQ0]; norm_num
  have hV1 : (vertexPts (fx ax, fx ay) (fx bx, fx by_)).1 =
      (fx ax + fx wx / 2 ^ 1 + √(1 - Q / 2 ^ 2) / √Q * fx (-wy),
        fx ay + fx wy / 2 ^ 1 + √(1 - Q / 2 ^ 2) / √Q * fx wx) := by
    simp only [vertexPts]
    rw [hen, hss]
    refine Prod.ext ?_ ?_
    · simp only [Prod.fst_add, Prod.smul_fst, Prod.fst_sub, smul_eq_mul, Prod.snd_sub, hw1, hw2, fx_neg]
      ring
    · simp only [Prod.snd_add, Prod.smul_snd, Prod.snd_sub, smul_eq_mul, Prod.fst_sub, hw1, hw2]
      ring
  have hV2 : (vertexPts (fx ax, fx ay) (fx bx, fx by_)).2 =
      (fx ax + fx wx / 2 ^ 1 - √(1 - Q / 2 ^ 2) / √Q * fx (-wy),
        fx ay + fx wy / 2 ^ 1 - √(1 - Q / 2 ^ 2) / √Q * fx wx) := by
    simp only [vertexPts]
    rw [hen, hss]
    refine Prod.ext ?_ ?_
    · simp only [Prod.fst_add, Prod.fst_sub, Prod.smul_fst, smul_eq_mul, Prod.snd_sub, hw1, hw2, fx_neg]
      ring
    · simp only [Prod.snd_add, Prod.snd_sub, Prod.smul_snd, smul_eq_mul, Prod.fst_sub, hw1, hw2]
      ring
  rw [hV1, hV2]
  exact ⟨ivMem_hi_le (mem_distIv (Iv.mem_add hmx hox) (Iv.mem_add hmy hoy) lx ly),
    ivMem_hi_le (mem_distIv (Iv.mem_sub hmx hox) (Iv.mem_sub hmy hoy) lx ly)⟩

end BHH.W2.TabB
