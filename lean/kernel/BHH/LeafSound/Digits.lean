/-
Module D, part 2a: base-3 edge states (`idx3`) and edge bitmasks, as computed by the leaf code.
-/
import BHH.LeafSound.Geo

open BHH.Cert

namespace BHH

/-- the value of a base-3 digit list `st` (digit `p` has weight `3^p`) -/
def val3 : List ℕ → ℕ
  | [] => 0
  | s :: rest => s + 3 * val3 rest

lemma val3_digit : ∀ (st : List ℕ), (∀ s ∈ st, s < 3) → ∀ p, p < st.length →
    val3 st / 3 ^ p % 3 = st.getD p 0
  | [], _, p, hp => by simp at hp
  | s :: rest, h, p, hp => by
    have hs : s < 3 := h s (by simp)
    have hrest : ∀ t ∈ rest, t < 3 := fun t ht => h t (by simp [ht])
    cases p with
    | zero => simp [val3]; omega
    | succ p =>
      have hp' : p < rest.length := by simpa using hp
      have ih := val3_digit rest hrest p hp'
      simp only [val3, List.getD_cons_succ]
      rw [pow_succ', ← Nat.div_div_eq_div_mul]
      have : (s + 3 * val3 rest) / 3 = val3 rest := by omega
      rw [this, ih]

/-- the code's fold equals `val3` -/
lemma fold_idx3 (st : List ℕ) :
    (st.zip (List.range st.length)).foldl (fun acc (sp : ℕ × ℕ) => acc + sp.1 * pow3 sp.2) 0 = val3 st := by
  -- generalize: foldl from acc over the zip with an offset
  have key : ∀ (l : List ℕ) (off acc : ℕ),
      (l.zip ((List.range l.length).map (· + off))).foldl (fun acc (sp : ℕ × ℕ) => acc + sp.1 * pow3 sp.2) acc
        = acc + 3 ^ off * val3 l := by
    intro l
    induction l with
    | nil => intro off acc; simp [val3]
    | cons s rest ih =>
      intro off acc
      rw [List.length_cons, List.range_succ_eq_map]
      simp only [List.map_cons, List.map_map, List.zip_cons_cons, List.foldl_cons, zero_add]
      have : (List.map ((fun x => x + off) ∘ Nat.succ) (List.range rest.length))
          = (List.range rest.length).map (· + (off + 1)) := by
        apply List.map_congr_left; intro a _; simp; omega
      rw [this, ih (off + 1)]
      simp [val3, pow3, pow_succ]; ring
  have := key st 0 0
  simpa using this

lemma val3_lt3 : ∀ (st : List ℕ), (∀ s ∈ st, s < 3) → val3 st < 3 ^ st.length
  | [], _ => by simp [val3]
  | s :: rest, h => by
    have hs := h s (by simp)
    have := val3_lt3 rest (fun t ht => h t (by simp [ht]))
    simp only [val3, List.length_cons, pow_succ]; omega

end BHH
