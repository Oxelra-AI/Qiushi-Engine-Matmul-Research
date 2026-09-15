import QiushiMatmul
import FrozenRegistry.AdditionalSources

open Lean Meta Elab Command

set_option maxHeartbeats 0
set_option maxRecDepth 100000

private def natValue? (e : Expr) : MetaM (Option Nat) := do
  let e ← whnf e
  match e with
  | .lit (.natVal n) => return some n
  | _ => return e.nat?

private partial def natList? (e : Expr) : MetaM (Option (List Nat)) := do
  let e ← whnf e
  if e.isAppOf ``List.nil then return some []
  if e.isAppOfArity ``List.cons 3 then
    let args := e.getAppArgs
    let some n ← natValue? args[1]! | return none
    let some ns ← natList? args[2]! | return none
    return some (n :: ns)
  return none

private def spanBasis? (e : Expr) : MetaM (Option (List Nat)) := do
  let mut e ← whnfCore e
  for _ in [:100] do
    if e.isAppOfArity ``QiushiMatmul.spanCodes 1 then
      return ← natList? e.getAppArgs[0]!
    let some next ← unfoldDefinition? e | return none
    e ← whnfCore next
  return none

private partial def matrixCode? (e : Expr) : MetaM (Option Nat) := do
  if e.isAppOfArity ``QiushiMatmul.codeMat 1 then
    return ← natValue? e.getAppArgs[0]!
  if e.isAppOfArity ``HAdd.hAdd 6 then
    let args := e.getAppArgs
    let some a ← matrixCode? args[4]! | return none
    let some b ← matrixCode? args[5]! | return none
    return some (a ^^^ b)
  let some next ← unfoldDefinition? e | return none
  matrixCode? next

private partial def kernelCodes? (e : Expr) : MetaM (Option (List Nat)) := do
  if e.isAppOfArity ``QiushiMatmul.kerEvalFunc 1 then
    let some c ← matrixCode? e.getAppArgs[0]! | return none
    return some [c]
  if e.isAppOf ``Min.min then
    let args := e.getAppArgs
    let some a ← kernelCodes? args[args.size - 2]! | return none
    let some b ← kernelCodes? args[args.size - 1]! | return none
    return some (a ++ b)
  let some next ← unfoldDefinition? e | return none
  kernelCodes? (← withTransparency .reducible (whnf next))

private partial def kernelSpace? (e : Expr) : MetaM (Option String) := do
  if e.isAppOfArity ``QiushiMatmul.kerEvalFunc 1 then
    return some s!"QiushiMatmul.kerEvalFunc ({← ppExpr e.getAppArgs[0]!})"
  if e.isAppOf ``Min.min then
    let args := e.getAppArgs
    let some a ← kernelSpace? args[args.size - 2]! | return none
    let some b ← kernelSpace? args[args.size - 1]! | return none
    return some s!"({a} ⊓ {b})"
  let some next ← unfoldDefinition? e | return none
  kernelSpace? (← withTransparency .reducible (whnf next))

private def matchSpace : Fin 2 → Submodule QiushiMatmul.F2 QiushiMatmul.Mat3
  | ⟨0, _⟩ => QiushiMatmul.spanCodes [1]
  | ⟨1, _⟩ => QiushiMatmul.spanCodes [2, 3]

run_cmd liftTermElabM do
  let e ← Lean.Elab.Term.elabTerm (← `(matchSpace 1)) none
  unless (← spanBasis? e) == some [2, 3] do
    throwError "Match-defined basis normalization failed"
  let inline ← Lean.Elab.Term.elabTerm (← `(
    match (1 : Fin 2).val with
    | 0 => QiushiMatmul.spanCodes [1]
    | _ => QiushiMatmul.spanCodes [2, 3])) none
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
  unless (← spanBasis? (← instantiateMVars inline)) == some [2, 3] do
    throwError "Inline match basis normalization failed"

private def recordCandidate (name : Name) (application : String) (type : Expr) :
    MetaM Bool := do
  if !type.isAppOfArity ``QiushiMatmul.QuotientRankAtLeast 2 then return false
  let args := type.getAppArgs
  let some bound ← natValue? args[1]! | return false
  let basis ← spanBasis? args[0]!
  let kernels ← if basis.isNone then kernelCodes? args[0]! else pure none
  let kernelSpace ← if kernels.isSome then kernelSpace? args[0]! else pure none
  let env ← getEnv
  let moduleName := match env.getModuleIdxFor? name with
    | some idx => env.header.moduleNames[idx.toNat]!.toString
    | none => "unknown"
  let row := Json.mkObj [
    ("theorem", toJson application), ("module", toJson moduleName),
    ("bound", toJson bound), ("basis", toJson basis),
    ("kernels", toJson kernels), ("kernel_space", toJson kernelSpace),
    ("space", toJson (toString (← ppExpr args[0]!)))]
  logInfo m!"REGISTRY_CANDIDATE {row.compress}"
  return true

run_cmd liftTermElabM do
  let env ← getEnv
  let mut count := 0
  let mut parameterized := 0
  for (name, info) in env.constants.toList do
    if !name.toString.startsWith "QiushiMatmul." then continue
    if ← recordCandidate name name.toString info.type then
      count := count + 1
      continue
    let .forallE _ domain body .default := info.type | continue
    if !body.isAppOfArity ``QiushiMatmul.QuotientRankAtLeast 2 then continue
    let domain ← whnf domain
    if !domain.isAppOfArity ``Fin 1 then continue
    let some size ← natValue? domain.getAppArgs[0]! | continue
    if size > 4096 then continue
    for i in [:size] do
      let argument ← Lean.Elab.Term.elabTerm (← `(( $(quote i) : Fin $(quote size)))) none
      Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
      let argument ← instantiateMVars argument
      if ← recordCandidate name s!"{name} ({i} : Fin {size})" (body.instantiate1 argument) then
        count := count + 1
        parameterized := parameterized + 1
  logInfo m!"REGISTRY_PARAMETERIZED {parameterized}"
  logInfo m!"REGISTRY_COUNT {count}"
