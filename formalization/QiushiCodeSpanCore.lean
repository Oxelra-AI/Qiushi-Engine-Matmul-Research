import QiushiCodeSpanBridgeCore

/-!
Compatibility layer for generated source dispatch modules.

Generated files use the name `spanContainsCodeCore`; the canonical
bridge exports `spanContainsCode`.  This file makes the names definitionally
identical and reuses the bridge theorem, so generated dispatch files
can compile against the shared source definitions.
-/

namespace QiushiMatmul

abbrev spanContainsCodeCore (basis : List Nat) (n : Nat) : Bool :=
  spanContainsCode basis n

theorem spanContainsCodeCore_implies_mem_spanCodes (basis : List Nat) (n : Nat)
    (h : spanContainsCodeCore basis n = true) :
    codeMat n ∈ spanCodes basis :=
  spanContainsCode_implies_mem_spanCodes basis n h

end QiushiMatmul
