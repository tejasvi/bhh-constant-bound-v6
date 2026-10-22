import Lean
open Lean

/-! Kernel replay of the constants of the given modules on top of an environment that imports everything they
import except themselves.  usage: `lean --run ReplayMods.lean M1 M2 ...` (with LEAN_PATH set).  Each constant of the
given modules is re-checked by the kernel (`Lean.Environment.replay`), against the `.olean` files that `LEAN_PATH`
selects for the other modules. -/

unsafe def main (args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  let mods : Array Name := args.toArray.map String.toName
  let modSet : NameSet := mods.foldl (·.insert ·) {}
  let mut newConsts : Std.HashMap Name ConstantInfo := {}
  let mut imps : NameSet := {}
  for m in mods do
    let path ← findOLean m
    let (md, _) ← readModuleData path
    for c in md.constants do
      newConsts := newConsts.insert c.name c
    for i in md.imports do
      unless modSet.contains i.module do imps := imps.insert i.module
  IO.println s!"{mods.size} modules, {newConsts.size} constants to replay, {imps.size} base imports"
  let env ← importModules (imps.toArray.map fun n => { module := n }) {} 0
  IO.println s!"base environment: {env.constants.fold (fun n _ _ => n + 1) 0} constants"
  let kenv ← env.toKernelEnv.replay newConsts
  let missing := newConsts.toList.filter fun (n, ci) => !ci.isUnsafe && !ci.isPartial && (kenv.find? n).isNone
  let skipped := newConsts.toList.filter fun (_, ci) => ci.isUnsafe || ci.isPartial
  IO.println s!"replay OK: {kenv.constants.fold (fun n _ _ => n + 1) 0} constants; not added: {missing.length}; skipped (unsafe/partial): {skipped.length} {(skipped.map (·.1)).take 10}"
  return 0
