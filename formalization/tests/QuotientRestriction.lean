import QiushiQuotientRestriction

open Matrix BigOperators
open QiushiMatmul QiushiMatmul.QuotientRestriction

noncomputable section

-- Pin the convention independently of the exported linear-map definitions.
example (W : Submodule F2 Mat3) (X : Mat3) :
    X ∈ inputAnnihilator W ↔
      ∀ A ∈ W, (∑ a : Coord9, A a.1 a.2 * X a.1 a.2) = 0 :=
  mem_inputAnnihilator W X

example (A X : Mat3) :
    matrixDual A X = Matrix.trace (A * X.transpose) := matrixDual_trace A X

example (W : Submodule F2 Mat3) :
    (Mat3 ⧸ W) ≃ₗ[F2] Module.Dual F2 (inputAnnihilator W) := quotientEquiv W

example (W : Submodule F2 Mat3) (A : Mat3) (X : inputAnnihilator W) :
    quotientEquiv W (Submodule.Quotient.mk A) X =
      ∑ a : Coord9, A a.1 a.2 * (X : Mat3) a.1 a.2 := quotientEquiv_mk W A X

-- No assumptions about W, its dimension, a basis, or r being positive.
example (W : Submodule F2 Mat3) (r : Nat) (A B C : Fin r -> Mat3) :
    (∀ b c : Coord9, tensorASlice b c +
      (∑ t : Fin r, (B t b.1 b.2 * C t c.1 c.2) • A t) ∈ W) ↔
    (∀ X : inputAnnihilator W, ∀ Y : Mat3,
      (X : Mat3) * Y = ∑ t : Fin r,
        ((∑ a : Coord9, A t a.1 a.2 * (X : Mat3) a.1 a.2) *
          (∑ b : Coord9, B t b.1 b.2 * Y b.1 b.2)) • C t) :=
  quotient_identity_iff_restricted_mul W A B C

example (W : Submodule F2 Mat3) (r : Nat) :
    Nonempty (QuotientTensorDecomp W r) ↔ Nonempty (RestrictedDecomp W r) :=
  nonempty_quotient_iff_restricted W r

example (W : Submodule F2 Mat3) (n : Nat) :
    QuotientRankAtLeast W n ↔
      ∀ (r : Nat) (left : Fin r -> ((inputAnnihilator W) →ₗ[F2] F2))
        (right : Fin r -> (Mat3 →ₗ[F2] F2)) (output : Fin r -> Mat3),
        (∀ X : inputAnnihilator W, ∀ Y : Mat3,
          (X : Mat3) * Y = ∑ t : Fin r, (left t X * right t Y) • output t) -> n ≤ r :=
  quotientRankAtLeast_iff_restricted_mul W n

example (W : Submodule F2 Mat3) (n : Nat) :
    (∃ r : Nat, r ≤ n ∧ Nonempty (QuotientTensorDecomp W r)) ↔
      ∃ r : Nat, r ≤ n ∧ Nonempty (RestrictedDecomp W r) :=
  rankAtMost_iff_restricted W n

example : inputAnnihilator (⊥ : Submodule F2 Mat3) = ⊤ := inputAnnihilator_bot
example : inputAnnihilator (⊤ : Submodule F2 Mat3) = ⊥ := inputAnnihilator_top
example (W : Submodule F2 Mat3) : inputAnnihilator (inputAnnihilator W) = W :=
  inputAnnihilator_involutive W

-- An off-diagonal test distinguishes coordinate pairing from trace(A * X).
example : codeMat 8 ∈ inputAnnihilator (spanCodes [2]) := by
  change matrixDual (codeMat 8) ∈ (spanCodes [2]).dualAnnihilator
  apply (Submodule.mem_dualAnnihilator _).mpr
  have h : spanCodes [2] ≤ LinearMap.ker (matrixDual (codeMat 8)) := by
    apply Submodule.span_le.mpr
    rintro A ⟨c, hc, rfl⟩
    simp only [List.mem_singleton] at hc
    subst c
    change matrixDual (codeMat 8) (codeMat 2) = 0
    decide
  exact fun A hA => h hA

example : codeMat 2 ∉ inputAnnihilator (spanCodes [2]) := by
  intro h
  have hz := (mem_inputAnnihilator _ _).mp h (codeMat 2)
    (Submodule.subset_span ⟨2, by simp, rfl⟩)
  have hn : matrixDual (codeMat 2) (codeMat 2) ≠ 0 := by decide
  exact hn hz

-- A zero-dimensional input has an actual zero-term algorithm.
example : Nonempty (RestrictedDecomp (⊤ : Submodule F2 Mat3) 0) := by
  apply (nonempty_quotient_iff_restricted _ 0).mp
  exact ⟨{
    A := Fin.elim0
    B := Fin.elim0
    C := Fin.elim0
    quotient_identity := fun _ _ => Submodule.mem_top }⟩

-- At W = 0, the same coefficient statement is full matrix multiplication.
example (r : Nat) (A B C : Fin r -> Mat3) :
    (∀ b c : Coord9, tensorASlice b c +
      (∑ t : Fin r, (B t b.1 b.2 * C t c.1 c.2) • A t) ∈
        (⊥ : Submodule F2 Mat3)) ↔
      ∀ X Y : Mat3, X * Y = bilinearAlgorithm A B C X Y := by
  rw [quotient_identity_iff_restricted_mul, inputAnnihilator_bot]
  simp only [Subtype.forall, Submodule.mem_top, forall_const]

#print axioms matrixDual_trace
#print axioms mem_iff_annihilator
#print axioms inputAnnihilator_involutive
#print axioms restrictCoefficient_surjective
#print axioms quotientEquiv
#print axioms quotientEquiv_mk
#print axioms quotient_identity_iff_restricted_mul
#print axioms toRestricted
#print axioms toQuotient
#print axioms nonempty_quotient_iff_restricted
#print axioms rankAtMost_iff_restricted
#print axioms quotientRankAtLeast_iff_restricted
#print axioms quotientRankAtLeast_iff_restricted_mul

-- Reject extra transitive axioms rather than merely printing a diagnostic.
run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let declarations := #[
    ``matrixDual, ``matrixDual_apply, ``matrixDual_comm, ``matrixDual_trace,
    ``inputAnnihilator, ``mem_inputAnnihilator, ``mem_iff_annihilator,
    ``inputAnnihilator_bot, ``inputAnnihilator_top, ``inputAnnihilator_involutive,
    ``restrictCoefficient, ``restrictCoefficient_apply, ``restrictCoefficient_ker,
    ``restrictCoefficient_surjective, ``quotientEquiv, ``quotientEquiv_mk,
    ``quotient_identity_iff_restricted_mul, ``RestrictedDecomp, ``toRestricted,
    ``toQuotient, ``nonempty_quotient_iff_restricted, ``rankAtMost_iff_restricted,
    ``quotientRankAtLeast_iff_restricted, ``quotientRankAtLeast_iff_restricted_mul]
  for decl in declarations do
    let axioms ← Lean.collectAxioms decl
    for dependency in axioms do
      unless allowed.contains dependency do
        throwError "{decl}: forbidden axiom {dependency}"
  Lean.logInfo m!"Standard-axiom guard passed for {declarations.size} declarations."
