import tools.ReplayRoots

open Lean QiushiReplay

private def expectFailure (label : String) (action : IO Nat) : IO Unit := do
  let failed ← try
    discard action
    pure false
  catch _ => pure true
  unless failed do throw <| IO.userError s!"accepted invalid case: {label}"

private unsafe def runReplayTests : IO Unit := do
  initSearchPath (← findSysroot)
  Lean.withImportModules #[{module := `Init}] {} fun env => do
    let all := env.constants.map₁
    discard <| replayRoots all [`Nat.add, `Nat.rec, `True.intro, `Quot.sound]
    expectFailure "empty roots" (replayRoots all [])
    expectFailure "absent root" (replayRoots all [`Nonexistent])
    let good : ConstantInfo := .thmInfo {
      name := `ReplayFixture.good, levelParams := [],
      type := mkConst `True, value := mkConst `True.intro }
    discard <| replayRoots (all.insert good.name good) [good.name]
    let bad : ConstantInfo := .thmInfo {
      name := `ReplayFixture.bad, levelParams := [],
      type := mkConst `False, value := mkConst `True.intro }
    expectFailure "false theorem" (replayRoots (all.insert bad.name bad) [bad.name])
    let ax : ConstantInfo := .axiomInfo {
      name := `ReplayFixture.assumption, levelParams := [],
      type := mkConst `False, isUnsafe := false }
    expectFailure "extra axiom" (replayRoots (all.insert ax.name ax) [ax.name])
    let transitive : ConstantInfo := .thmInfo {
      name := `ReplayFixture.transitive, levelParams := [],
      type := mkConst `False, value := mkConst ax.name }
    expectFailure "transitive extra axiom"
      (replayRoots ((all.insert ax.name ax).insert transitive.name transitive) [transitive.name])
    let missing : ConstantInfo := .thmInfo {
      name := `ReplayFixture.missing, levelParams := [],
      type := mkConst `True, value := mkConst `Nonexistent }
    expectFailure "missing dependency"
      (replayRoots (all.insert missing.name missing) [missing.name])
    for safety in [DefinitionSafety.unsafe, DefinitionSafety.partial] do
      let defn : ConstantInfo := .defnInfo {
        name := `ReplayFixture.unchecked, levelParams := [], type := mkConst `Nat,
        value := mkNatLit 0, hints := .opaque, safety }
      expectFailure "unchecked dependency"
        (replayRoots (all.insert defn.name defn) [defn.name])
    let some (.recInfo recursor) := all[`Nat.rec]? |
      throw <| IO.userError "missing test recursor"
    let forged : ConstantInfo := .recInfo { recursor with type := mkConst `False }
    expectFailure "forged recursor" (replayRoots (all.insert forged.name forged) [forged.name])
    IO.println "ReplayRoots tests passed (valid closures and nine invalid cases)"

#eval runReplayTests
