import QiushiCodeSpanBridgeCore

/-! Small separating functionals certify strict subspace containments.
These witnesses establish that selected occupation rows are among the
nonzero proper quotient subspaces quantified over in the report. -/

open BigOperators
namespace QiushiMatmul

def matrixPair (D M : Mat3) : F2 := ∑ i, ∑ j, D i j * M i j

def matrixPairLinear (D : Mat3) : Mat3 →ₗ[F2] F2 where
  toFun := matrixPair D
  map_add' X Y := by simp [matrixPair, mul_add, Finset.sum_add_distrib]
  map_smul' a X := by simp [matrixPair, Finset.mul_sum, mul_left_comm]

theorem spanCodes_pair_zero (basis : List Nat) (D : Mat3)
    (h : ∀ c ∈ basis, matrixPair D (codeMat c) = 0)
    {M : Mat3} (hM : M ∈ spanCodes basis) : matrixPair D M = 0 := by
  have hs : spanCodes basis ≤ LinearMap.ker (matrixPairLinear D) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨c, hc, rfl⟩
    exact h c hc
  exact hs hM

def strictSpanCheck (lower upper : List Nat) (x d e y : Nat) : Bool :=
  spanContainsCode upper x &&
  lower.all (fun c => decide (matrixPair (codeMat d) (codeMat c) = 0)) &&
  decide (matrixPair (codeMat d) (codeMat x) ≠ 0) &&
  upper.all (fun c => decide (matrixPair (codeMat e) (codeMat c) = 0)) &&
  decide (matrixPair (codeMat e) (codeMat y) ≠ 0)

theorem strictSpanCheck_sound (lower upper : List Nat) (x d e y : Nat)
    (hle : spanCodes lower ≤ spanCodes upper)
    (h : strictSpanCheck lower upper x d e y = true) :
    spanCodes lower < spanCodes upper ∧ spanCodes upper < ⊤ := by
  simp only [strictSpanCheck, Bool.and_eq_true, List.all_eq_true,
    decide_eq_true_eq] at h
  rcases h with ⟨⟨⟨⟨hx, hd⟩, hdx⟩, he⟩, hey⟩
  constructor
  · apply lt_of_le_not_ge hle
    intro hu
    exact hdx (spanCodes_pair_zero lower (codeMat d) hd
      (hu (spanContainsCode_implies_mem_spanCodes upper x hx)))
  · apply lt_of_le_not_ge le_top
    intro ht
    exact hey (spanCodes_pair_zero upper (codeMat e) he (ht (Submodule.mem_top)))

end QiushiMatmul
