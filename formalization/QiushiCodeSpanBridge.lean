import QiushiCodeSpanBridgeCore
import QiushiOrbit486QuotientLabels

/-!
# Code-level span bridge: compatibility aggregate

Re-exports the orbit-agnostic bridge from `QiushiCodeSpanBridgeCore` and adds
orbit-486-specific convenience lemmas.  Existing modules that import
`QiushiCodeSpanBridge` continue to work unchanged.

New modules should prefer `import QiushiCodeSpanBridgeCore` directly when only
the generic bridge is needed.
-/

namespace QiushiMatmul

-- ============================================================================
-- Orbit-486 convenience lemmas
-- ============================================================================

/-- For occupation rows: if `p ∈ sourceMask486 i`, then
    `codeMat (sectionCode486 p) ∈ spanCodes (sourceBasis486 i)`. -/
theorem sourceMask486_implies_section_mem_span (i : Fin 169) (p : Fin 127)
    (h : p ∈ sourceMask486 i) :
    codeMat (sectionCode486 p) ∈ spanCodes (sourceBasis486 i) := by
  rw [sourceMask486_exact_section_membership] at h
  exact spanContainsCode_implies_mem_spanCodes (sourceBasis486 i) (sectionCode486 p) h

/-- For dead witnesses: each dead point's section representative lies in
    its witness subspace. -/
theorem deadPoint486_section_in_witness_span (d : Fin 87) :
    codeMat (sectionCode486 (deadPoint486 d)) ∈ spanCodes (deadWitnessBasis486 d) :=
  spanContainsCode_implies_mem_spanCodes
    (deadWitnessBasis486 d)
    (sectionCode486 (deadPoint486 d))
    (deadPoint486_section_mem_deadWitness486 d)

end QiushiMatmul
