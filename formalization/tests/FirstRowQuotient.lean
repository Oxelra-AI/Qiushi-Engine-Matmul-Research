import QiushiFirstRowQuotient

noncomputable section

open Matrix BigOperators QiushiMatmul
open scoped TensorProduct

-- Exact public types, including the original coded subspace and all nine B entries.
example : (Mat3 ⧸ spanCodes [4,2,1]) ≃ₗ[F2] Matrix (Fin 2) (Fin 3) F2 :=
  firstRowQuotientEquiv

example (M : Mat3) :
    firstRowQuotientEquiv (Submodule.Quotient.mk M) = fun i j => M i.succ j :=
  firstRowQuotientEquiv_mk M

example : Module.finrank F2 (Mat3 ⧸ firstRowFamily) = 6 := by
  rw [firstRowQuotientEquiv.finrank_eq]
  simp [Mat23, Module.finrank_matrix]

example : Module.finrank F2 Mat3 = 9 := by
  simp [Mat3, I3, Module.finrank_matrix]

example : Module.finrank F2 FirstRowOutputSupport = 6 := by
  rw [firstRowOutputEquiv.finrank_eq]
  simp [Mat23, I3, Module.finrank_matrix]

example (r : Nat) (D : QuotientTensorDecomp (spanCodes [4,2,1]) r) :
    RectTensorDecomp r := D.toRect

example (r : Nat) (D : RectTensorDecomp r) :
    QuotientTensorDecomp (spanCodes [4,2,1]) r := D.toFirstRowQuotient

example (r : Nat) (D : QuotientTensorDecomp firstRowFamily r) (t : Fin r) :
    D.toRect.B t = D.B t := rfl

example (r : Nat) (D : RectTensorDecomp r) (t : Fin r) (k : Fin 3) :
    D.toFirstRowQuotient.C t 0 k = 0 := rfl

example (r : Nat) :
    Nonempty (QuotientTensorDecomp (spanCodes [4,2,1]) r) ↔
      Nonempty (RectTensorDecomp r) := firstRow_quotient_decomp_iff r

example (n : Nat) :
    QuotientRankAtLeast (spanCodes [4,2,1]) n ↔
      ∀ r : Nat, RectTensorDecomp r → n ≤ r := firstRow_quotient_rankAtLeast_iff n

example (r : Nat) : NormalizedFirstRowDecomp r ≃ RectTensorDecomp r :=
  normalizedFirstRowDecompEquiv r

example (r : Nat) (D : RectTensorDecomp r) : D.toFirstRowQuotient.toRect = D :=
  D.toFirstRowQuotient_toRect

example :
    ((Mat3 ⧸ spanCodes [4,2,1]) ⊗[F2] (Mat3 ⊗[F2] FirstRowOutputSupport)) ≃ₗ[F2]
      (Mat23 ⊗[F2] (Mat3 ⊗[F2] Mat23)) := firstRowTensorEquiv

example : firstRowTensorEquiv firstRowSupportedTensor = rectMatmulTensor :=
  firstRowTensorEquiv_tensor

example :
    TensorProduct.map (LinearMap.id : (Mat3 ⧸ firstRowFamily) →ₗ[F2] _)
      (TensorProduct.map (LinearMap.id : Mat3 →ₗ[F2] Mat3)
        (LinearMap.range padLowerRows).subtype) firstRowSupportedTensor =
      TensorProduct.map firstRowFamily.mkQ
        (LinearMap.id : (Mat3 ⊗[F2] Mat3) →ₗ[F2] _) fullMatmulTensor :=
  firstRowSupportedTensor_inclusion

example (X : Matrix (Fin 2) (Fin 3) F2) (Y : Matrix (Fin 3) (Fin 3) F2)
    (i : Fin 2) (k : Fin 3) :
    (∑ a : Coord23, ∑ b : Coord9,
      X a.1 a.2 * Y b.1 b.2 * rectTensorEntry a b (i,k)) = (X * Y) i k :=
  rectTensorEntry_contract X Y i k

-- Fail the test if any audited declaration acquires a nonstandard axiom.
/-- info: 'QiushiMatmul.firstRowFamily_eq_ker_lowerRows' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QiushiMatmul.firstRowFamily_eq_ker_lowerRows

/-- info: 'QiushiMatmul.firstRowQuotientEquiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QiushiMatmul.firstRowQuotientEquiv

/-- info: 'QiushiMatmul.rectTensorEntry_contract' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QiushiMatmul.rectTensorEntry_contract

/-- info: 'QiushiMatmul.firstRowQuotientEquiv_slice' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QiushiMatmul.firstRowQuotientEquiv_slice

/-- info: 'QiushiMatmul.firstRowQuotientEquiv_slice_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QiushiMatmul.firstRowQuotientEquiv_slice_zero

/-- info: 'QiushiMatmul.QuotientTensorDecomp.toRect' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QiushiMatmul.QuotientTensorDecomp.toRect

/-- info: 'QiushiMatmul.RectTensorDecomp.toFirstRowQuotient' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QiushiMatmul.RectTensorDecomp.toFirstRowQuotient

/-- info: 'QiushiMatmul.firstRow_quotient_decomp_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QiushiMatmul.firstRow_quotient_decomp_iff

/-- info: 'QiushiMatmul.firstRow_quotient_rankAtLeast_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QiushiMatmul.firstRow_quotient_rankAtLeast_iff

/-- info: 'QiushiMatmul.normalizedFirstRowDecompEquiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QiushiMatmul.normalizedFirstRowDecompEquiv

/-- info: 'QiushiMatmul.firstRowTensorEquiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QiushiMatmul.firstRowTensorEquiv

/-- info: 'QiushiMatmul.firstRowTensorEquiv_tensor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QiushiMatmul.firstRowTensorEquiv_tensor

/-- info: 'QiushiMatmul.firstRowSupportedTensor_inclusion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QiushiMatmul.firstRowSupportedTensor_inclusion

end
