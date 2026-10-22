/-
The window-2 pass (paper Lemma 4.3) as a finite automaton (core Lean only).

A state describes the window (the last one or two points, newest first): `two` (window has two points),
`same` (the two window points lie in one component of the graph so far), `d0`, `d1` (their degrees so far, capped
at 2) and `u` (the number of points that have left the window with degree < 2; the pass stops when it reaches 2).
`step s a1 a2` adds a point with the edges `a1` (to the newest window point) and `a2` (to the older one); `none`
means the pass has returned 0 (the graph is disconnected, or two vertices have degree < 2).
-/

namespace W2C

structure St where
  two : Bool
  same : Bool
  d0 : Nat
  d1 : Nat
  u : Nat
  deriving DecidableEq, Repr, Inhabited, BEq

def b2n (b : Bool) : Nat := if b then 1 else 0
def cap2 (n : Nat) : Nat := Min.min n 2

/-- the state after the first point `y_0` -/
def St.init : St := ⟨false, false, 0, 0, 0⟩

/-- add a point with edge `a1` to the newest window point and `a2` to the older one -/
def St.step (s : St) (a1 a2 : Bool) : Option St :=
  if !s.two then
    some ⟨true, a1, b2n a1, cap2 (s.d0 + b2n a1), s.u⟩
  else
    let d1f := cap2 (s.d1 + b2n a2)              -- final degree of the point leaving the window
    let u' := s.u + (if d1f < 2 then 1 else 0)
    if 2 ≤ u' then none
    else if !(a2 || s.same) then none            -- its component would not meet the new window
    else some ⟨true, a1 || (a2 && s.same), b2n a1 + b2n a2, cap2 (s.d0 + b2n a1), u'⟩

/-- twice the closing value `Λ` of a state after the last point (`0`, `1` or `2`) -/
def St.close2 (s : St) : Nat :=
  if s.same then
    let n := s.u + (if s.d0 < 2 then 1 else 0) + (if s.d1 < 2 then 1 else 0)
    if n == 0 then 2 else if n == 1 then 1 else 0
  else 0

/-- closing value after adding the last point with edges `a1`, `a2` -/
def St.closeStep2 (s : St) (a1 a2 : Bool) : Nat :=
  match s.step a1 a2 with
  | none => 0
  | some s' => s'.close2

/-- The reachable states, in breadth-first order from `init` (computed with fuel; 17 states). -/
def reachable : List St :=
  let inputs : List (Bool × Bool) := [(false, false), (false, true), (true, false), (true, true)]
  let rec go : Nat → List St → List St → List St
    | 0, seen, _ => seen
    | fuel + 1, seen, [] => let _ := fuel; seen
    | fuel + 1, seen, s :: queue =>
      let nexts := inputs.filterMap fun (a1, a2) => s.step a1 (if s.two then a2 else false)
      let new := nexts.foldl (fun acc t => if acc.contains t || seen.contains t then acc else acc ++ [t]) []
      go fuel (seen ++ new) (queue ++ new)
  go 100 [St.init] [St.init]

end W2C
