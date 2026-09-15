import QiushiWcOrbit146Consumer

open QiushiMatmul BigOperators

example (c : Fin 512) :
    1 ≤ ∑ i : Fin 7, if o146CoverB_wc i c.val = true then o146Lambda_wc i else 0 :=
  o146CodeCoverage_wc c

run_cmd do
  let axioms ← Lean.collectAxioms ``o146CodeCoverage_wc
  for ax in axioms do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
      throwError "Unexpected axiom {ax}"
  Lean.logInfo m!"COVER146_AXIOMS {axioms}"
