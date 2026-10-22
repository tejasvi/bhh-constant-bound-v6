/-
Module C, probability layer: the code part of `ProbStripsProp` (`StripCodeProp`, BHH/Box/StripDefs.lean).
The loop of `probStrips` keeps `pin ∋ Σ innerVal` and `outer ∋ Σ outerVal` over the strips processed so far
(`cdfIv` encloses `cdfR` by `CdfIvProp`; module A's interval lemmas for the arithmetic).
-/
import BHH.Box.StripDefs
import BHH.Box.CdfIv

open BHH.Cert Real

namespace BHH

noncomputable section

namespace PB

/-- one step of the strip loop of `probStrips` (verbatim) -/
def stripStep (P Q : PtBox) : Iv × Iv → ℤ × ℤ × Iv × Iv → Iv × Iv :=
  fun (pin, outer) (x0, x1, F0, F1) =>
      let px := Iv.sub F1 F0
      let amax := Max.max x0.natAbs x1.natAbs
      let amin : Nat := if x0 ≤ 0 ∧ 0 ≤ x1 then 0 else Min.min x0.natAbs x1.natAbs
      let pin' :=
        if (amax : Int) < ONE then
          let yb := (Iv.sqrt (Iv.sub (Iv.int 1) (Iv.sqr (Iv.pt amax)))).lo
          if 0 < yb then
            let G := Iv.sub (cdfIv P.yl P.yh Q.yl Q.yh yb) (cdfIv P.yl P.yh Q.yl Q.yh (-yb))
            Iv.add pin (Iv.mul G px)
          else pin
        else pin
      let outer' :=
        if (amin : Int) < ONE then
          let yb := (Iv.sqrt (Iv.sub (Iv.int 1) (Iv.sqr (Iv.pt amin)))).hi
          let G := if (P.yh == P.yl ∧ Q.yh == Q.yl) then
                     (if (P.yl - Q.yl).natAbs ≤ yb.toNat then Iv.int 1 else Iv.int 0)
                   else Iv.sub (cdfIv P.yl P.yh Q.yl Q.yh yb) (cdfIv P.yl P.yh Q.yl Q.yh (-yb))
          Iv.add outer (Iv.mul G px)
        else outer
      (pin', outer')

lemma probStrips_eq (P Q : PtBox) : probStrips P Q =
    if (P.xh - Q.xl) - (P.xl - Q.xh) ≤ 0 then (0, 0)
    else
      let xt := (List.range 9).map fun (t : Nat) =>
        (P.xl - Q.xh) + ((P.xh - Q.xl) - (P.xl - Q.xh)) * (t : Int) / 8
      let F := xt.map fun z => cdfIv P.xl P.xh Q.xl Q.xh z
      let strips := (List.range 8).map fun t =>
        (xt.getD t 0, xt.getD (t + 1) 0, F.getD t default, F.getD (t + 1) default)
      let r := strips.foldl (stripStep P Q) (Iv.int 0, Iv.int 0)
      (Max.max r.1.lo 0, Max.max (ONE - r.2.hi) 0) := rfl

/-! ## one strip -/

lemma mem_int_one' : ivMem 1 (Iv.int 1) := by have h := Iv.mem_int 1; rwa [Int.cast_one] at h
lemma mem_int_zero' : ivMem 0 (Iv.int 0) := by have h := Iv.mem_int 0; rwa [Int.cast_zero] at h

lemma cdfY_mem (P Q : PtBox) (hPy : P.yl ≤ P.yh) (hQy : Q.yl ≤ Q.yh) (z : ℤ) :
    ivMem (cdfY P Q (fx z)) (cdfIv P.yl P.yh Q.yl Q.yh z) :=
  cdfIvProp P.yl P.yh Q.yl Q.yh z hPy hQy

lemma stripStep_spec (P Q : PtBox) (hPy : P.yl ≤ P.yh) (hQy : Q.yl ≤ Q.yh) {pin outer : Iv} {sp so : ℝ}
    (hp : ivMem sp pin) (ho : ivMem so outer) {x0 x1 : ℤ} {F0 F1 : Iv}
    (hF0 : ivMem (cdfX P Q (fx x0)) F0) (hF1 : ivMem (cdfX P Q (fx x1)) F1) :
    ivMem (sp + innerVal P Q x0 x1) (stripStep P Q (pin, outer) (x0, x1, F0, F1)).1 ∧
    ivMem (so + outerVal P Q x0 x1) (stripStep P Q (pin, outer) (x0, x1, F0, F1)).2 := by
  have hpx := Iv.mem_sub hF1 hF0
  constructor
  · -- the inner sum
    have hcode : (stripStep P Q (pin, outer) (x0, x1, F0, F1)).1 =
        (if (stripAmax x0 x1 : ℤ) < ONE then
          (if 0 < stripYbIn x0 x1 then
            Iv.add pin (Iv.mul (Iv.sub (cdfIv P.yl P.yh Q.yl Q.yh (stripYbIn x0 x1))
              (cdfIv P.yl P.yh Q.yl Q.yh (-stripYbIn x0 x1))) (Iv.sub F1 F0))
           else pin)
         else pin) := by
      simp only [stripStep]; rfl
    rw [hcode]
    unfold innerVal
    by_cases h1 : (stripAmax x0 x1 : ℤ) < ONE
    · rw [if_pos h1]
      by_cases h2 : 0 < stripYbIn x0 x1
      · rw [if_pos h2, if_pos ⟨h1, h2⟩]
        exact Iv.mem_add hp (Iv.mem_mul (Iv.mem_sub (cdfY_mem P Q hPy hQy _) (cdfY_mem P Q hPy hQy _)) hpx)
      · rw [if_neg h2, if_neg (fun h => h2 h.2), add_zero]; exact hp
    · rw [if_neg h1, if_neg (fun h => h1 h.1), add_zero]; exact hp
  · -- the outer sum
    have hcode : (stripStep P Q (pin, outer) (x0, x1, F0, F1)).2 =
        (if (stripAmin x0 x1 : ℤ) < ONE then
          Iv.add outer (Iv.mul (if (P.yh == P.yl ∧ Q.yh == Q.yl) then
              (if (P.yl - Q.yl).natAbs ≤ (stripYbOut x0 x1).toNat then Iv.int 1 else Iv.int 0)
            else Iv.sub (cdfIv P.yl P.yh Q.yl Q.yh (stripYbOut x0 x1))
              (cdfIv P.yl P.yh Q.yl Q.yh (-stripYbOut x0 x1))) (Iv.sub F1 F0))
         else outer) := by
      simp only [stripStep]; rfl
    rw [hcode]
    unfold outerVal
    by_cases h1 : (stripAmin x0 x1 : ℤ) < ONE
    · rw [if_pos h1, if_pos h1]
      refine Iv.mem_add ho (Iv.mem_mul ?_ hpx)
      by_cases hd : P.yh = P.yl ∧ Q.yh = Q.yl
      · have hd' : (P.yh == P.yl) = true ∧ (Q.yh == Q.yl) = true := by simp [hd.1, hd.2]
        rw [if_pos hd, if_pos hd']
        split_ifs
        · exact mem_int_one'
        · exact mem_int_zero'
      · have hd' : ¬ ((P.yh == P.yl) = true ∧ (Q.yh == Q.yl) = true) := by simpa using hd
        rw [if_neg hd, if_neg hd']
        exact Iv.mem_sub (cdfY_mem P Q hPy hQy _) (cdfY_mem P Q hPy hQy _)
    · rw [if_neg h1, if_neg h1, add_zero]; exact ho

/-! ## the loop -/

lemma foldl_strip (P Q : PtBox) (hPy : P.yl ≤ P.yh) (hQy : Q.yl ≤ Q.yh) :
    ∀ (L : List (ℤ × ℤ × Iv × Iv)) (pin outer : Iv) (sp so : ℝ), ivMem sp pin → ivMem so outer →
    (∀ e ∈ L, ivMem (cdfX P Q (fx e.1)) e.2.2.1 ∧ ivMem (cdfX P Q (fx e.2.1)) e.2.2.2) →
    ivMem (sp + (L.map fun e => innerVal P Q e.1 e.2.1).sum) (L.foldl (stripStep P Q) (pin, outer)).1 ∧
    ivMem (so + (L.map fun e => outerVal P Q e.1 e.2.1).sum) (L.foldl (stripStep P Q) (pin, outer)).2
  | [], pin, outer, sp, so, hp, ho, _ => by simpa using ⟨hp, ho⟩
  | ⟨x0, x1, F0, F1⟩ :: L, pin, outer, sp, so, hp, ho, hL => by
    simp only [List.foldl_cons, List.map_cons, List.sum_cons]
    have hh := hL ⟨x0, x1, F0, F1⟩ List.mem_cons_self
    have h1 := stripStep_spec P Q hPy hQy hp ho hh.1 hh.2
    rcases hs : stripStep P Q (pin, outer) (x0, x1, F0, F1) with ⟨pin', outer'⟩
    rw [hs] at h1
    have h2 := foldl_strip P Q hPy hQy L pin' outer' _ _ h1.1 h1.2
      (fun e he => hL e (List.mem_cons_of_mem _ he))
    rw [← add_assoc, ← add_assoc]
    exact h2

lemma list_range_sum (f : ℕ → ℝ) : ∀ n, ((List.range n).map f).sum = ∑ t ∈ Finset.range n, f t
  | 0 => by simp
  | n + 1 => by
    rw [List.range_succ, List.map_append, List.sum_append, list_range_sum f n, Finset.sum_range_succ]
    simp

/-- the data of strip `t` -/
def stripTuple (P Q : PtBox) (t : ℕ) : ℤ × ℤ × Iv × Iv :=
  (stripX P Q t, stripX P Q (t + 1), cdfIv P.xl P.xh Q.xl Q.xh (stripX P Q t),
    cdfIv P.xl P.xh Q.xl Q.xh (stripX P Q (t + 1)))

/-! ## the theorem -/

theorem stripCodeProp : StripCodeProp := by
  intro P Q hPx hPy hQx hQy
  rw [probStrips_eq]
  constructor
  · intro hwz; rw [if_pos hwz]
  · intro hwz
    rw [if_neg (not_le.mpr hwz)]
    dsimp only
    -- the strip list
    set xt := (List.range 9).map fun (t : ℕ) => (P.xl - Q.xh) + ((P.xh - Q.xl) - (P.xl - Q.xh)) * (t : ℤ) / 8
      with hxt
    have hxtget : ∀ t, t < 9 → xt.getD t 0 = stripX P Q t := by
      intro t ht
      rw [hxt, List.getD_eq_getElem _ _ (by simpa using ht)]
      simp [stripX]
    have hFget : ∀ t, t < 9 → (xt.map fun z => cdfIv P.xl P.xh Q.xl Q.xh z).getD t default =
        cdfIv P.xl P.xh Q.xl Q.xh (stripX P Q t) := by
      intro t ht
      rw [List.getD_eq_getElem _ _ (by simpa [hxt] using ht), List.getElem_map, ← hxtget t ht,
        List.getD_eq_getElem _ _ (by simpa [hxt] using ht)]
    have hstrips : ((List.range 8).map fun t => (xt.getD t 0, xt.getD (t + 1) 0,
        (xt.map fun z => cdfIv P.xl P.xh Q.xl Q.xh z).getD t default,
        (xt.map fun z => cdfIv P.xl P.xh Q.xl Q.xh z).getD (t + 1) default)) = (List.range 8).map (stripTuple P Q) := by
      apply List.map_congr_left
      intro t ht
      rw [List.mem_range] at ht
      rw [hxtget t (by omega), hxtget (t + 1) (by omega), hFget t (by omega), hFget (t + 1) (by omega)]
      rfl
    rw [hstrips]
    have helem : ∀ e ∈ (List.range 8).map (stripTuple P Q),
        ivMem (cdfX P Q (fx e.1)) e.2.2.1 ∧ ivMem (cdfX P Q (fx e.2.1)) e.2.2.2 := by
      intro e he
      obtain ⟨t, _, rfl⟩ := List.mem_map.mp he
      exact ⟨cdfIvProp _ _ _ _ _ hPx hQx, cdfIvProp _ _ _ _ _ hPx hQx⟩
    have key := foldl_strip P Q hPy hQy ((List.range 8).map (stripTuple P Q)) (Iv.int 0) (Iv.int 0) 0 0
      mem_int_zero' mem_int_zero' helem
    rw [zero_add, zero_add] at key
    simp only [List.map_map, Function.comp_def] at key
    have es1 : ((List.range 8).map (fun t => innerVal P Q (stripTuple P Q t).1 (stripTuple P Q t).2.1)).sum =
        ∑ t ∈ Finset.range 8, innerVal P Q (stripX P Q t) (stripX P Q (t + 1)) := by
      rw [list_range_sum]; rfl
    have es2 : ((List.range 8).map (fun t => outerVal P Q (stripTuple P Q t).1 (stripTuple P Q t).2.1)).sum =
        ∑ t ∈ Finset.range 8, outerVal P Q (stripX P Q t) (stripX P Q (t + 1)) := by
      rw [list_range_sum]; rfl
    rw [es1, es2] at key
    set r := ((List.range 8).map (stripTuple P Q)).foldl (stripStep P Q) (Iv.int 0, Iv.int 0) with hr
    set S1 := ∑ t ∈ Finset.range 8, innerVal P Q (stripX P Q t) (stripX P Q (t + 1))
    set S2 := ∑ t ∈ Finset.range 8, outerVal P Q (stripX P Q t) (stripX P Q (t + 1))
    have hS := SC_pos
    obtain ⟨k1, -⟩ := key.1
    obtain ⟨-, k2⟩ := key.2
    constructor
    · -- fx (max r.1.lo 0) ≤ max S1 0
      rw [fx_eq]
      rcases le_total r.1.lo 0 with h | h
      · rw [max_eq_right h]; simp
      · rw [max_eq_left h]
        have : (r.1.lo : ℝ) / SC ≤ S1 := by rw [div_le_iff₀ hS]; exact k1
        exact le_trans this (le_max_left _ _)
    · -- fx (max (ONE - r.2.hi) 0) ≤ max (1 - S2) 0
      rw [fx_eq]
      rcases le_total (ONE - r.2.hi) 0 with h | h
      · rw [max_eq_right h]; simp
      · rw [max_eq_left h]
        have : (((ONE - r.2.hi : ℤ)) : ℝ) / SC ≤ 1 - S2 := by
          rw [div_le_iff₀ hS]; push_cast; rw [ONE_cast]; linarith
        exact le_trans this (le_max_left _ _)

end PB

end

end BHH
