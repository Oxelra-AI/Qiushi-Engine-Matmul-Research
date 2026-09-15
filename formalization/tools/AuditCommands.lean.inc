open Lean Elab Command in
elab "audit_decl " id:ident : command => do
  let name := id.getId
  let env <- getEnv
  let some info := env.find? name | throwError "absent declaration: {name}"
  if info.isUnsafe || info.isPartial then
    throwError "unsafe or partial declaration is skipped by leanchecker: {name}"
  let some idx := env.getModuleIdxFor? name |
    throwError "declaration is not imported: {name}"
  let some mod := env.header.moduleNames[idx.toNat]? |
    throwError "absent origin module: {name}"
  let ty <- liftTermElabM <| Meta.ppExpr info.type
  let axs <- collectAxioms name
  let obj := Json.mkObj [
    ("name", toJson name.toString),
    ("module", toJson mod.toString),
    ("universes", toJson (info.levelParams.map Name.toString)),
    ("type", toJson ty.pretty),
    ("axioms", toJson (axs.map Name.toString))]
  logInfo ("MATMUL_AUDIT_JSON " ++ obj.compress)

set_option pp.all true
set_option pp.proofs true
set_option pp.deepTerms true
set_option pp.universes true
set_option pp.fullNames true
set_option pp.maxSteps 10000000
set_option maxRecDepth 10000
