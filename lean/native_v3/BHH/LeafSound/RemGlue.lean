/-
Module D, part 4: the code's remainder quantities (`moments`, `remPair`) bound the real ones of the vertex lemma.
-/
import BHH.LeafSound.UnionGlue

open BHH.Cert Real

noncomputable section

namespace BHH

/-! ## moments of a code rectangle -/

/-- the real half-sides of a code rectangle -/
def halfOf (P : PtBox) : ℝ × ℝ := ((fx P.xh - fx P.xl) / 2, (fx P.yh - fx P.yl) / 2)

lemma fx_ha {P : PtBox} (h : Even (P.xl + P.xh)) : fx P.ha = (fx P.xh - fx P.xl) / 2 := by
  unfold PtBox.ha
  have h' : Even (P.xh - P.xl) := by
    have : P.xh - P.xl = (P.xl + P.xh) - 2 * P.xl := by ring
    rw [this]; exact Even.sub h (even_two_mul _)
  obtain ⟨r, hr⟩ := h'
  have : (P.xh - P.xl) / 2 = r := by omega
  rw [this]; unfold fx
  have : (P.xh : ℝ) - P.xl = 2 * r := by exact_mod_cast (by omega : P.xh - P.xl = 2 * r)
  field_simp; linarith

lemma fx_hb {P : PtBox} (h : Even (P.yl + P.yh)) : fx P.hb = (fx P.yh - fx P.yl) / 2 := by
  unfold PtBox.hb
  have h' : Even (P.yh - P.yl) := by
    have : P.yh - P.yl = (P.yl + P.yh) - 2 * P.yl := by ring
    rw [this]; exact Even.sub h (even_two_mul _)
  obtain ⟨r, hr⟩ := h'
  have : (P.yh - P.yl) / 2 = r := by omega
  rw [this]; unfold fx
  have : (P.yh : ℝ) - P.yl = 2 * r := by exact_mod_cast (by omega : P.yh - P.yl = 2 * r)
  field_simp; linarith

/-- the four moment enclosures of a code rectangle -/
theorem moments_sound {P : PtBox} (hx : Even (P.xl + P.xh)) (hy : Even (P.yl + P.yh)) :
    ivMem (rectOf P).eps (moments P).1 ∧
    ivMem √(((halfOf P).1 ^ 2 + (halfOf P).2 ^ 2) / 3) (moments P).2.1 ∧
    ivMem (((halfOf P).1 ^ 2 + (halfOf P).2 ^ 2) / 3) (moments P).2.2.1 ∧
    ivMem ((halfOf P).1 ^ 4 / 5 + 2 * (halfOf P).1 ^ 2 * (halfOf P).2 ^ 2 / 9 + (halfOf P).2 ^ 4 / 5)
      (moments P).2.2.2 := by
  have ha : ivMem (halfOf P).1 (Iv.pt P.ha) := by
    have := Iv.mem_pt P.ha; rw [fx_ha hx] at this; exact this
  have hb : ivMem (halfOf P).2 (Iv.pt P.hb) := by
    have := Iv.mem_pt P.hb; rw [fx_hb hy] at this; exact this
  have ha2 := Iv.mem_sqr ha
  have hb2 := Iv.mem_sqr hb
  have hsum := Iv.mem_add ha2 hb2
  have hm2 := Iv.mem_divNat hsum (by norm_num : 0 < 3)
  unfold moments
  simp only
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- ε = √((xh - xl)² + (yh - yl)²) / 2 = √(a² + b²) with a, b the half-sides
    have e : (rectOf P).eps = √((halfOf P).1 ^ 2 + (halfOf P).2 ^ 2) := by
      unfold Rect.eps rectOf halfOf; simp only
      rw [show ((fx P.xh - fx P.xl) / 2) ^ 2 + ((fx P.yh - fx P.yl) / 2) ^ 2
          = ((fx P.xh - fx P.xl) ^ 2 + (fx P.yh - fx P.yl) ^ 2) / 2 ^ 2 by ring]
      rw [Real.sqrt_div' _ (by positivity : (0:ℝ) ≤ 2 ^ 2), Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)]
    rw [e]; exact Iv.mem_sqrt hsum
  · push_cast at hm2; exact Iv.mem_sqrt hm2
  · push_cast at hm2; exact hm2
  · have h1 := Iv.mem_divNat (Iv.mem_sqr ha2) (by norm_num : 0 < 5)
    have h2 := Iv.mem_divNat (Iv.mem_mulNat (Iv.mem_mul ha2 hb2) 2) (by norm_num : 0 < 9)
    have h3 := Iv.mem_divNat (Iv.mem_sqr hb2) (by norm_num : 0 < 5)
    have := Iv.mem_add (Iv.mem_add h1 h2) h3
    push_cast at this
    convert this using 1; ring

/-! ## the distance quantities of a pair -/

lemma fx_div2e_pt (n : ℤ) : fx n / 2 ^ PR = (n : ℝ) / (2 : ℝ) ^ (2 * PR) := by
  unfold fx; rw [div_div, ← pow_add]; ring_nf

/-- `d2mnI ∋ (d^-)^2` and `dmn ∋ d^-` for an exact `d2mn` at scale `2^-2PR` -/
lemma mem_d2I (d2 : ℤ) : ivMem ((d2 : ℝ) / (2 : ℝ) ^ (2 * PR)) (Iv.div2e (Iv.pt d2) PR) := by
  have := Iv.mem_div2e (Iv.mem_pt d2) PR
  rwa [fx_div2e_pt] at this

lemma ONE_sq4_cast : ((4 * ONE * ONE : ℤ) : ℝ) / (2 : ℝ) ^ (2 * PR) = 4 := by
  push_cast; rw [ONE_cast]; unfold SC; rw [pow_mul']; field_simp

/-- the bound `T(w) ≤ motion` of the code, from enclosures of its ingredients -/
lemma Tseg_le_motion {dlo dhi w : ℝ} {first : Bool} {c1 c0 tcap : ℤ} {dl : Iv}
    (hw : ivMem w dl) (hc1 : 0 ≤ c1) (hlam : (if first then 1 / √(4 - dhi ^ 2) else 0) ≤ fx c1)
    (hmu : (if first then 0 else 2 * Real.arcsin (min dhi 2 / 2) - 2 * Real.arcsin (dlo / 2)) ≤ fx c0)
    (ht : min (w / dlo) π ≤ fx tcap) (hw0 : 0 ≤ w) :
    Tseg dlo dhi first w ≤ fx (shrU (c1 * dl.hi) PR + c0 + tcap) := by
  unfold Tseg
  have hS : (0:ℝ) < 2 ^ PR := by positivity
  have hmul : (if first then 1 / √(4 - dhi ^ 2) else 0) * w ≤ fx (shrU (c1 * dl.hi) PR) := by
    have h1 := le_shrU (c1 * dl.hi) PR
    have hwhi : w ≤ fx dl.hi := ivMem_hi_le hw
    have hc1' : (0:ℝ) ≤ fx c1 := by unfold fx; positivity
    calc (if first then 1 / √(4 - dhi ^ 2) else 0) * w ≤ fx c1 * fx dl.hi := by
          apply mul_le_mul hlam hwhi hw0 hc1'
      _ = ((c1 * dl.hi : ℤ) : ℝ) / 2 ^ PR / 2 ^ PR := by unfold fx; push_cast; ring
      _ ≤ ((shrU (c1 * dl.hi) PR : ℤ) : ℝ) / 2 ^ PR := by gcongr
      _ = fx (shrU (c1 * dl.hi) PR) := rfl
  have e : fx (shrU (c1 * dl.hi) PR + c0 + tcap) = fx (shrU (c1 * dl.hi) PR) + fx c0 + fx tcap := by
    unfold fx; push_cast; ring
  rw [e]
  cases first
  · simp only [Bool.false_eq_true, ite_false] at hlam hmu hmul ⊢
    have : (0:ℝ) * w = 0 := by ring
    linarith
  · simp only [ite_true] at hlam hmu hmul ⊢
    have : w / √(4 - dhi ^ 2) = 1 / √(4 - dhi ^ 2) * w := by ring
    linarith

end BHH
