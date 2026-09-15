import Lean.Replay

/-!
Fresh kernel replay of explicitly selected declarations and their dependencies.
The imported environment supplies data only: replay starts with mkEmptyEnvironment.
This uses Lean's unmodified Environment.replay, including its constructor and
recursor checks. It does not certify unrelated declarations in imported modules.
-/

open Lean

namespace QiushiReplay

def allowedAxiom (name : Name) : Bool :=
  name == `propext || name == `Classical.choice || name == `Quot.sound

def dependencies (ci : ConstantInfo) : NameSet :=
  let used := ci.getUsedConstantsAsSet
  match ci with
  | .inductInfo info => used ++ NameSet.ofList info.all
  | .quotInfo _ => used.insert `Eq
  | _ => used

def closure (all : Std.HashMap Name ConstantInfo) (roots : List Name) :
    IO (Std.HashMap Name ConstantInfo) := do
  if roots.isEmpty then throw <| IO.userError "no replay roots"
  let mut pending := roots.toArray
  let mut selected : Std.HashMap Name ConstantInfo := {}
  while !pending.isEmpty do
    let name := pending.back!
    pending := pending.pop
    if selected.contains name then continue
    let some ci := all[name]? |
      throw <| IO.userError s!"missing dependency: {name}"
    if ci.isUnsafe || ci.isPartial then
      throw <| IO.userError s!"unsafe or partial dependency: {name}"
    if ci matches .axiomInfo _ then
      unless allowedAxiom name do
        throw <| IO.userError s!"nonstandard axiom: {name}"
    selected := selected.insert name ci
    for dep in dependencies ci do pending := pending.push dep
  return selected

def replayRoots (all : Std.HashMap Name ConstantInfo) (roots : List Name) : IO Nat := do
  let selected ← closure all roots
  let checked ← (← mkEmptyEnvironment).replay selected
  for name in roots do
    let some actual := checked.toKernelEnv.find? name |
      throw <| IO.userError s!"root absent after replay: {name}"
    let some expected := selected[name]? |
      throw <| IO.userError s!"root absent from dependency closure: {name}"
    unless actual.type == expected.type && actual.levelParams == expected.levelParams do
      throw <| IO.userError s!"root type changed: {name}"
  return selected.size

end QiushiReplay

unsafe def main (args : List String) : IO UInt32 := do
  let moduleList :: roots := args |
    throw <| IO.userError "usage: ReplayRoots <module[,module...]> <declaration> ..."
  if roots.isEmpty then throw <| IO.userError "no replay roots"
  let modules := moduleList.splitOn ","
  initSearchPath (← findSysroot)
  Lean.withImportModules (modules.toArray.map fun name => { module := name.toName }) {} fun env => do
    let names := roots.map String.toName
    let selected ← QiushiReplay.closure env.constants.map₁ names
    IO.println <| "QIUSHI_REPLAY_BEGIN " ++ (Json.mkObj [
      ("modules", toJson modules), ("roots", toJson roots),
      ("declarations", toJson selected.size)]).compress
    (← IO.getStdout).flush
    let count ← QiushiReplay.replayRoots env.constants.map₁ names
    IO.println <| "QIUSHI_REPLAY_PASS " ++ (Json.mkObj [
      ("modules", toJson modules), ("roots", toJson roots),
      ("declarations", toJson count)]).compress
    return 0
