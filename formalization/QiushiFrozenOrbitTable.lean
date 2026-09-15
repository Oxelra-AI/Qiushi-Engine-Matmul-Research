import QiushiCodeSpanBridgeCore
import QiushiOrbitTransport
import QiushiTransposeTransport

/-!
# Frozen orbit-table expansion

`FrozenOrbitTable.L0` expands the labels of 496 supplied representatives along
exact invertible matrix/transpose orbits. The checked transport API proves a
numeric lower bound on this function, not a quotient-rank theorem.

This module supplies neither the representative data nor their rank bounds,
orbit classification, or equality with the historical pickle's L0. Those are
separate data-binding and mathematical obligations. Overlapping orbits are
allowed: L0 takes the maximum of their labels, and is zero off their union.
-/

namespace QiushiMatmul

/-- Frozen representative codes and numeric labels; no classification or
rank-soundness hypothesis is implicit in the data structure. -/
structure FrozenOrbitTable where
  basis : Fin 496 → List Nat
  lower : Fin 496 → Nat

/-- Exact orbit membership, including the optional transpose. -/
def FrozenOrbitTable.OrbitImage (table : FrozenOrbitTable) (i : Fin 496)
    (W : Submodule F2 Mat3) : Prop :=
  ∃ P Q : Mat3, Nonempty (Invertible P) ∧ Nonempty (Invertible Q) ∧
    ∃ flip : Bool,
      W = actionW P Q
        (if flip then transposeW (spanCodes (table.basis i))
         else spanCodes (table.basis i))

/-- Mathematical orbit expansion, not a computable classifier or pickle lookup. -/
noncomputable def FrozenOrbitTable.L0 (table : FrozenOrbitTable)
    (W : Submodule F2 Mat3) : Nat := by
  classical
  exact Finset.univ.sup (fun i => if table.OrbitImage i W then table.lower i else 0)

/-- A single orbit witness suffices; consumers need not unfold the supremum. -/
theorem FrozenOrbitTable.lower_le_L0 (table : FrozenOrbitTable) (i : Fin 496)
    {W : Submodule F2 Mat3} (h : table.OrbitImage i W) :
    table.lower i ≤ table.L0 W := by
  classical
  have hi := Finset.le_sup
    (f := fun j => if table.OrbitImage j W then table.lower j else 0)
    (Finset.mem_univ i)
  simpa only [L0, if_pos h] using hi

/-- Two checked containments give exact equality under any linear map.
Pairs are `(target code, source preimage code)`. Source generators need only
lie in the span of the preimages, not occur literally among them. -/
theorem spanCodes_map_eq_of_code_pairs
    (basis : List Nat) (pairs : List (Nat × Nat)) (f : Mat3 →ₗ[F2] Mat3)
    (hPairs : ∀ e ∈ pairs,
      spanContainsCode basis e.2 = true ∧ f (codeMat e.2) = codeMat e.1)
    (hCover : ∀ c ∈ basis, spanContainsCode (pairs.map Prod.snd) c = true) :
    spanCodes (pairs.map Prod.fst) = (spanCodes basis).map f := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro M ⟨c, hc, rfl⟩
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hc
    exact ⟨codeMat e.2,
      spanContainsCode_implies_mem_spanCodes basis e.2 (hPairs e he).1,
      (hPairs e he).2⟩
  · have hBasis : spanCodes basis ≤ spanCodes (pairs.map Prod.snd) := by
      apply Submodule.span_le.mpr
      rintro M ⟨c, hc, rfl⟩
      exact spanContainsCode_implies_mem_spanCodes _ c (hCover c hc)
    have hImage : (spanCodes (pairs.map Prod.snd)).map f ≤
        spanCodes (pairs.map Prod.fst) := by
      apply Submodule.map_le_iff_le_comap.mpr
      apply Submodule.span_le.mpr
      rintro M ⟨c, hc, rfl⟩
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp hc
      change f (codeMat e.2) ∈ spanCodes (pairs.map Prod.fst)
      rw [(hPairs e he).2]
      exact Submodule.subset_span ⟨e.1, List.mem_map.mpr ⟨e, he, rfl⟩, rfl⟩
    exact (Submodule.map_mono hBasis).trans hImage

/-- Exact span transport using the existing orbit and transpose linear maps.
Invertibility of P is unnecessary for this equality; the orbit API below
additionally requires both determinants to be nonzero. -/
theorem spanCodes_action_eq_of_code_transport
    (basis : List Nat) (pairs : List (Nat × Nat))
    (P Q Qinv : Mat3) (flip : Bool)
    (hInv : Q.transpose * Qinv.transpose = 1)
    (hPairs : ∀ e ∈ pairs,
      spanContainsCode basis e.2 = true ∧
      P.transpose * (if flip then (codeMat e.2).transpose else codeMat e.2) *
        Qinv.transpose = codeMat e.1)
    (hCover : ∀ c ∈ basis, spanContainsCode (pairs.map Prod.snd) c = true) :
    spanCodes (pairs.map Prod.fst) =
      actionW P Q (if flip then transposeW (spanCodes basis) else spanCodes basis) := by
  let f := (actionALinearMap P Q).comp
    (if flip then transposeLinearMap else LinearMap.id)
  have hInv' : Q.transpose⁻¹ = Qinv.transpose := Matrix.inv_eq_right_inv hInv
  have hf (M : Mat3) : f M =
      P.transpose * (if flip then M.transpose else M) * Qinv.transpose := by
    cases flip <;> simp [f, actionALinearMap, actionA, hInv']
  have hEq := spanCodes_map_eq_of_code_pairs basis pairs f
    (fun e he => ⟨(hPairs e he).1, (hf _).trans (hPairs e he).2⟩) hCover
  rw [hEq]
  cases flip <;> simp [f, actionW, transposeW, Submodule.map_comp]

/-- Checked exact code transport establishes membership in a frozen orbit. -/
theorem frozenOrbitImage_of_code_transport
    (table : FrozenOrbitTable) (i : Fin 496) (pairs : List (Nat × Nat))
    (P Q Qinv : Mat3) (flip : Bool)
    (hP : P.det ≠ 0) (hQ : Q.det ≠ 0)
    (hInv : Q.transpose * Qinv.transpose = 1)
    (hPairs : ∀ e ∈ pairs,
      spanContainsCode (table.basis i) e.2 = true ∧
      P.transpose * (if flip then (codeMat e.2).transpose else codeMat e.2) *
        Qinv.transpose = codeMat e.1)
    (hCover : ∀ c ∈ table.basis i,
      spanContainsCode (pairs.map Prod.snd) c = true) :
    table.OrbitImage i (spanCodes (pairs.map Prod.fst)) := by
  refine ⟨P, Q,
    ⟨Matrix.invertibleOfIsUnitDet P (isUnit_iff_ne_zero.mpr hP)⟩,
    ⟨Matrix.invertibleOfIsUnitDet Q (isUnit_iff_ne_zero.mpr hQ)⟩, flip, ?_⟩
  exact spanCodes_action_eq_of_code_transport (table.basis i) pairs P Q Qinv flip
    hInv hPairs hCover

/-- Numerical frozen-L0 bound from one exact code-transport witness.
For literal tables, rewrite only `table.basis i` and `table.lower i` at the
chosen index; this theorem leaves the noncomputable supremum abstract. -/
theorem frozenL0_ge_of_code_transport
    (table : FrozenOrbitTable) (i : Fin 496) (pairs : List (Nat × Nat))
    (P Q Qinv : Mat3) (flip : Bool)
    (hP : P.det ≠ 0) (hQ : Q.det ≠ 0)
    (hInv : Q.transpose * Qinv.transpose = 1)
    (hPairs : ∀ e ∈ pairs,
      spanContainsCode (table.basis i) e.2 = true ∧
      P.transpose * (if flip then (codeMat e.2).transpose else codeMat e.2) *
        Qinv.transpose = codeMat e.1)
    (hCover : ∀ c ∈ table.basis i,
      spanContainsCode (pairs.map Prod.snd) c = true) :
    table.lower i ≤ table.L0 (spanCodes (pairs.map Prod.fst)) :=
  table.lower_le_L0 i
    (frozenOrbitImage_of_code_transport table i pairs P Q Qinv flip hP hQ hInv
      hPairs hCover)

end QiushiMatmul
