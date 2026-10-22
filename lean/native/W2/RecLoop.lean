/-
Loop lemmas for the production recursion `W2C.runT4`: the pre-merge sums `gEntry`/`vEntry`, `addList`,
`srcLoopF` and the row concatenation, as exact `Nat` sums.
-/
import Mathlib
import W2.RecArith

namespace BHH.W2

open W2C

/-- A `foldl` that adds `f D` for `D < n` is the finite sum. -/
lemma foldl_add_range (n : ℕ) (f : ℕ → ℕ) (a : ℕ) :
    (List.range n).foldl (fun acc D => acc + f D) a = a + ∑ D ∈ Finset.range n, f D := by
  induction n generalizing a with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, ih, Finset.sum_range_succ]
    simp only [List.foldl_cons, List.foldl_nil]
    ring

lemma gEntry_eq (pt : PassTab) (F : Array ℕ) (ns c D2 : ℕ) :
    gEntry pt F ns c D2 = ∑ D ∈ Finset.range 17,
      if pt.trans[(D * 2 + ns / 2) * 2 + ns % 2]! = D2 then F[c * 17 + D]! else 0 := by
  unfold gEntry
  have h : (fun acc D => if (pt.trans[(D * 2 + ns / 2) * 2 + ns % 2]! == D2) = true then acc + F[c * 17 + D]! else acc)
      = (fun acc D => acc + (if pt.trans[(D * 2 + ns / 2) * 2 + ns % 2]! = D2 then F[c * 17 + D]! else 0)) := by
    funext acc D
    by_cases hD : pt.trans[(D * 2 + ns / 2) * 2 + ns % 2]! = D2 <;> simp [hD]
  rw [h, foldl_add_range]; simp

lemma vEntry_eq (pt : PassTab) (F : Array ℕ) (ns c : ℕ) :
    vEntry pt F ns c = ∑ D ∈ Finset.range 17,
      pt.close2[(D * 2 + ns / 2) * 2 + ns % 2]! * F[c * 17 + D]! := by
  unfold vEntry
  rw [foldl_add_range]; simp

/-- `addList` adds `mulTop` at every listed index (each occurrence once). -/
lemma addList_spec (lower : Bool) (G1 G0 : Array ℕ) (o k1 k0 : ℕ) :
    ∀ (lst : List ℕ) (acc : Array ℕ), (∀ d ∈ lst, d < acc.size) →
      (addList lower G1 G0 o k1 k0 lst acc).size = acc.size ∧
      ∀ D2, (addList lower G1 G0 o k1 k0 lst acc)[D2]! =
        acc[D2]! + lst.count D2 * mulTop lower G1[o * 17 + D2]! G0[o * 17 + D2]! k1 k0
  | [], acc, _ => by simp [addList]
  | d :: rest, acc, h => by
    simp only [addList]
    have hd : d < acc.size := h d (by simp)
    set acc' := acc.set! d (acc[d]! + mulTop lower G1[o * 17 + d]! G0[o * 17 + d]! k1 k0)
    have hsz : acc'.size = acc.size := by simp [acc']
    have ih := addList_spec lower G1 G0 o k1 k0 rest acc' (by
      intro d' hd'; rw [hsz]; exact h d' (by simp [hd']))
    refine ⟨ih.1.trans hsz, fun D2 => ?_⟩
    rw [ih.2 D2]
    by_cases hD : D2 = d
    · subst hD
      have : acc'[D2]! = acc[D2]! + mulTop lower G1[o * 17 + D2]! G0[o * 17 + D2]! k1 k0 :=
        Array.getElem!_set!_self acc D2 _ hd
      rw [this, List.count_cons_self]; ring
    · have : acc'[D2]! = acc[D2]! := Array.getElem!_set!_ne acc d D2 _ (Ne.symm hD)
      rw [this, List.count_cons_of_ne (Ne.symm hD)]

/-- The table index and the pre-merge row of the source cell `c` for the target `(ir2, it2)`. -/
def idxOf (NR NT ND ir2 it2 c : ℕ) : ℕ := (c / NT * NR + ir2) * ND + (it2 + (NT - 1) - c % NT)

def oOf (NR NT ND NC nb ir2 it2 : ℕ) (cls1 : Array Bool) (c : ℕ) : ℕ :=
  (nb * 2 + (if cls1[idxOf NR NT ND ir2 it2 c]! then 1 else 0)) * NC + c

/-- `srcLoopF` as exact sums over the source cells. -/
lemma srcLoopF_spec (lower : Bool) (NR NT ND NC nb ir2 it2 : ℕ) (k1s k0s : Array ℕ) (cls1 : Array Bool)
    (G1 G0 V1 V0 : Array ℕ) (nz : Array (List ℕ)) :
    ∀ (n : ℕ) (acc : Array ℕ) (cacc : ℕ), (∀ o : ℕ, ∀ d ∈ nz[o]!, d < acc.size) →
      (srcLoopF lower NR NT ND NC nb ir2 it2 k1s k0s cls1 G1 G0 V1 V0 nz n acc cacc).1.size = acc.size ∧
      (∀ D2, (srcLoopF lower NR NT ND NC nb ir2 it2 k1s k0s cls1 G1 G0 V1 V0 nz n acc cacc).1[D2]! =
        acc[D2]! + ∑ c ∈ Finset.range n,
          (nz[oOf NR NT ND NC nb ir2 it2 cls1 c]!).count D2 *
            mulTop lower G1[oOf NR NT ND NC nb ir2 it2 cls1 c * 17 + D2]!
              G0[oOf NR NT ND NC nb ir2 it2 cls1 c * 17 + D2]!
              k1s[idxOf NR NT ND ir2 it2 c]! k0s[idxOf NR NT ND ir2 it2 c]!) ∧
      (srcLoopF lower NR NT ND NC nb ir2 it2 k1s k0s cls1 G1 G0 V1 V0 nz n acc cacc).2 =
        cacc + ∑ c ∈ Finset.range n,
          mulTop lower V1[oOf NR NT ND NC nb ir2 it2 cls1 c]! V0[oOf NR NT ND NC nb ir2 it2 cls1 c]!
            k1s[idxOf NR NT ND ir2 it2 c]! k0s[idxOf NR NT ND ir2 it2 c]! := by
  intro n
  induction n with
  | zero => intro acc cacc _; simp [srcLoopF]
  | succ c ih =>
    intro acc cacc hnz
    have hA := addList_spec lower G1 G0 (oOf NR NT ND NC nb ir2 it2 cls1 c) k1s[idxOf NR NT ND ir2 it2 c]!
      k0s[idxOf NR NT ND ir2 it2 c]! nz[oOf NR NT ND NC nb ir2 it2 cls1 c]! acc (hnz _)
    have ih' := ih (addList lower G1 G0 (oOf NR NT ND NC nb ir2 it2 cls1 c) k1s[idxOf NR NT ND ir2 it2 c]!
      k0s[idxOf NR NT ND ir2 it2 c]! nz[oOf NR NT ND NC nb ir2 it2 cls1 c]! acc)
      (cacc + mulTop lower V1[oOf NR NT ND NC nb ir2 it2 cls1 c]! V0[oOf NR NT ND NC nb ir2 it2 cls1 c]!
        k1s[idxOf NR NT ND ir2 it2 c]! k0s[idxOf NR NT ND ir2 it2 c]!) (by
      intro o' d hd; rw [hA.1]; exact hnz o' d hd)
    have e : srcLoopF lower NR NT ND NC nb ir2 it2 k1s k0s cls1 G1 G0 V1 V0 nz (c + 1) acc cacc =
        srcLoopF lower NR NT ND NC nb ir2 it2 k1s k0s cls1 G1 G0 V1 V0 nz c
          (addList lower G1 G0 (oOf NR NT ND NC nb ir2 it2 cls1 c) k1s[idxOf NR NT ND ir2 it2 c]!
            k0s[idxOf NR NT ND ir2 it2 c]! nz[oOf NR NT ND NC nb ir2 it2 cls1 c]! acc)
          (cacc + mulTop lower V1[oOf NR NT ND NC nb ir2 it2 cls1 c]! V0[oOf NR NT ND NC nb ir2 it2 cls1 c]!
            k1s[idxOf NR NT ND ir2 it2 c]! k0s[idxOf NR NT ND ir2 it2 c]!) := rfl
    rw [e]
    refine ⟨ih'.1.trans hA.1, fun D2 => ?_, ?_⟩
    · rw [ih'.2.1 D2, hA.2 D2, Finset.sum_range_succ]; ring
    · rw [ih'.2.2, Finset.sum_range_succ]; ring

end BHH.W2
