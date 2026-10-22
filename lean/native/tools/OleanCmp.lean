import Lean
open Lean

/-! Compare the constants of two `.olean` files of the same module (names, kinds, universe parameters, types, values,
inductive/constructor/recursor data).  usage: `lean --run OleanCmp.lean A1.olean B1.olean [A2.olean B2.olean ...]`. -/

def hintsStr : ReducibilityHints → String
  | .opaque => "opaque"
  | .abbrev => "abbrev"
  | .regular h => s!"regular {h}"

def safetyStr : DefinitionSafety → String
  | .unsafe => "unsafe"
  | .safe => "safe"
  | .partial => "partial"

def quotStr : QuotKind → String
  | .type => "type"
  | .ctor => "ctor"
  | .lift => "lift"
  | .ind => "ind"

def ciMeta (c : ConstantInfo) : String :=
  match c with
  | .axiomInfo v => s!"axiom unsafe={v.isUnsafe}"
  | .defnInfo v => s!"def safety={safetyStr v.safety} hints={hintsStr v.hints} all={v.all}"
  | .thmInfo v => s!"thm all={v.all}"
  | .opaqueInfo v => s!"opaque unsafe={v.isUnsafe} all={v.all}"
  | .quotInfo v => s!"quot {quotStr v.kind}"
  | .inductInfo v => s!"induct params={v.numParams} indices={v.numIndices} all={v.all} ctors={v.ctors} rec={v.isRec} unsafe={v.isUnsafe} refl={v.isReflexive} nested={v.numNested}"
  | .ctorInfo v => s!"ctor induct={v.induct} cidx={v.cidx} params={v.numParams} fields={v.numFields} unsafe={v.isUnsafe}"
  | .recInfo v => s!"rec all={v.all} params={v.numParams} indices={v.numIndices} motives={v.numMotives} minors={v.numMinors} k={v.k} unsafe={v.isUnsafe} rules={v.rules.map (fun r => (r.ctor, r.nfields))}"

def ruleRhs (c : ConstantInfo) : List Expr :=
  match c with
  | .recInfo v => v.rules.map (·.rhs)
  | _ => []

def valueOf (c : ConstantInfo) : Option Expr :=
  match c with
  | .defnInfo v => some v.value
  | .thmInfo v => some v.value
  | .opaqueInfo v => some v.value
  | _ => none

unsafe def cmpPair (a b : System.FilePath) : IO Bool := do
  let (ma, ra) ← readModuleData a
  let (mb, rb) ← readModuleData b
  let mut bad : Array String := #[]
  if ma.imports.map (·.module) != mb.imports.map (·.module) then bad := bad.push "imports differ"
  if ma.constNames != mb.constNames then bad := bad.push s!"constNames differ ({ma.constNames.size} vs {mb.constNames.size})"
  if ma.constants.size != mb.constants.size then bad := bad.push "constant counts differ"
  for (ca, cb) in ma.constants.zip mb.constants do
    if ca.name != cb.name || ca.levelParams != cb.levelParams || ciMeta ca != ciMeta cb || !(ca.type == cb.type)
        || !(valueOf ca == valueOf cb) || !(ruleRhs ca == ruleRhs cb) then
      bad := bad.push s!"constant {ca.name} / {cb.name} differs"
  IO.println s!"{if bad.isEmpty then "SAME" else "DIFF"} {a.fileName.getD ""}: {ma.constants.size} constants, imports {ma.imports.size} {bad.toList.take 5}"
  ra.free; rb.free
  return bad.isEmpty

unsafe def main (args : List String) : IO UInt32 := do
  let rec go : List String → IO Nat
    | a :: b :: rest => do
      let ok ← cmpPair a b
      return (if ok then 0 else 1) + (← go rest)
    | _ => return 0
  let nbad ← go args
  IO.println s!"pairs with differences: {nbad}"
  return (if nbad == 0 then 0 else 1)
