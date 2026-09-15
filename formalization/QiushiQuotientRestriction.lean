import QiushiBilinearSemantics

/-!
# Quotient coefficients and restricted matrix multiplication

The pairing is `sum (i,j), A i j * X i j = trace (A * X.transpose)`.
For every coefficient subspace W, quotienting by W is equivalent, at every
decomposition length, to computing X * Y for X in its coordinate annihilator.
Restricted first-input forms are arbitrary linear forms, not assumed extensions.
-/

open Matrix BigOperators

namespace QiushiMatmul.QuotientRestriction

private def matrixCoords : Mat3 ≃ₗ[F2] (Coord9 -> F2) where
  toFun A a := A a.1 a.2
  invFun f i j := f (i, j)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The actual coordinate pairing, as an equivalence with the full dual. -/
def matrixDual : Mat3 ≃ₗ[F2] Module.Dual F2 Mat3 :=
  (matrixCoords.trans (dotProductEquiv F2 Coord9)).trans matrixCoords.dualMap

@[simp] theorem matrixDual_apply (A X : Mat3) :
    matrixDual A X = ∑ a : Coord9, A a.1 a.2 * X a.1 a.2 := rfl

theorem matrixDual_comm (A X : Mat3) : matrixDual A X = matrixDual X A := by
  simp only [matrixDual_apply, mul_comm]

theorem matrixDual_trace (A X : Mat3) :
    matrixDual A X = Matrix.trace (A * X.transpose) := by
  simp [matrixDual_apply, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Fintype.sum_prod_type]

/-- Matrices representing functionals that vanish on W, not W itself. -/
def inputAnnihilator (W : Submodule F2 Mat3) : Submodule F2 Mat3 :=
  W.dualAnnihilator.comap matrixDual.toLinearMap

theorem mem_inputAnnihilator (W : Submodule F2 Mat3) (X : Mat3) :
    X ∈ inputAnnihilator W ↔ ∀ A ∈ W, matrixDual A X = 0 := by
  change matrixDual X ∈ W.dualAnnihilator ↔ _
  rw [Submodule.mem_dualAnnihilator]
  simp only [matrixDual_comm]

/-- Dual separation supplies the reverse implication for every W. -/
theorem mem_iff_annihilator (W : Submodule F2 Mat3) (A : Mat3) :
    A ∈ W ↔ ∀ X ∈ inputAnnihilator W, matrixDual A X = 0 := by
  constructor
  · intro hA X hX
    exact (mem_inputAnnihilator W X).mp hX A hA
  · intro h
    apply (Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff W A).mp
    intro f hf
    obtain ⟨X, rfl⟩ := matrixDual.surjective f
    rw [matrixDual_comm]
    exact h X hf

@[simp] theorem inputAnnihilator_bot :
    inputAnnihilator (⊥ : Submodule F2 Mat3) = ⊤ := by
  ext X
  simp [mem_inputAnnihilator]

@[simp] theorem inputAnnihilator_top :
    inputAnnihilator (⊤ : Submodule F2 Mat3) = ⊥ := by
  ext X
  rw [mem_inputAnnihilator, mem_iff_annihilator (⊥ : Submodule F2 Mat3) X]
  simp only [inputAnnihilator_bot, Submodule.mem_top, forall_const]
  constructor <;> intro h A <;> rw [matrixDual_comm] <;> exact h A

@[simp] theorem inputAnnihilator_involutive (W : Submodule F2 Mat3) :
    inputAnnihilator (inputAnnihilator W) = W := by
  ext X
  rw [mem_inputAnnihilator, mem_iff_annihilator W X]
  simp only [matrixDual_comm]

/-- Restrict coefficient evaluation to the genuine first-input domain. -/
def restrictCoefficient (W : Submodule F2 Mat3) :
    Mat3 →ₗ[F2] Module.Dual F2 (inputAnnihilator W) :=
  (inputAnnihilator W).dualRestrict.comp matrixDual.toLinearMap

@[simp] theorem restrictCoefficient_apply (W : Submodule F2 Mat3)
    (A : Mat3) (X : inputAnnihilator W) :
    restrictCoefficient W A X = matrixDual A X := rfl

theorem restrictCoefficient_ker (W : Submodule F2 Mat3) :
    LinearMap.ker (restrictCoefficient W) = W := by
  ext A
  simp only [LinearMap.mem_ker, LinearMap.ext_iff, restrictCoefficient_apply,
    LinearMap.zero_apply, Subtype.forall, ← mem_iff_annihilator]

theorem restrictCoefficient_surjective (W : Submodule F2 Mat3) :
    Function.Surjective (restrictCoefficient W) :=
  (Subspace.dualRestrict_surjective (W := inputAnnihilator W)).comp matrixDual.surjective

/-- Canonical coefficient quotient / restricted-input dual equivalence. -/
noncomputable def quotientEquiv (W : Submodule F2 Mat3) :
    (Mat3 ⧸ W) ≃ₗ[F2] Module.Dual F2 (inputAnnihilator W) :=
  (Submodule.quotEquivOfEq _ _ (restrictCoefficient_ker W).symm).trans
    ((restrictCoefficient W).quotKerEquivOfSurjective (restrictCoefficient_surjective W))

@[simp] theorem quotientEquiv_mk (W : Submodule F2 Mat3) (A : Mat3)
    (X : inputAnnihilator W) :
    quotientEquiv W (Submodule.Quotient.mk A) X = matrixDual A X := by
  simp only [quotientEquiv, LinearEquiv.trans_apply, Submodule.quotEquivOfEq_mk,
    LinearMap.quotKerEquivOfSurjective_apply_mk, restrictCoefficient_apply]

private theorem slice_pairing_single (X : Mat3) (b c : Coord9) :
    matrixDual (tensorASlice b c) X =
      (X * Matrix.single b.1 b.2 (1 : F2)) c.1 c.2 := by
  simp [matrixDual_apply, tensorASlice, tensorEntry, Matrix.mul_apply,
    Matrix.single_apply, Fintype.sum_prod_type, ite_and, mul_ite, ite_mul]
  split_ifs <;> simp_all

private theorem mul_contract_slices (X Y : Mat3) (c : Coord9) :
    (X * Y) c.1 c.2 =
      ∑ b : Coord9, Y b.1 b.2 * matrixDual (tensorASlice b c) X := by
  rw [← tensorEntry_contract X Y c.1 c.2, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  simp only [matrixDual_apply, tensorASlice, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  ring

private theorem algorithm_single {r : Nat} (A B C : Fin r -> Mat3)
    (X : Mat3) (b c : Coord9) :
    bilinearAlgorithm A B C X (Matrix.single b.1 b.2 1) c.1 c.2 =
      ∑ t : Fin r, matrixDual (A t) X * B t b.1 b.2 * C t c.1 c.2 := by
  simp [bilinearAlgorithm, matrixDual_apply, Matrix.single_apply,
    Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    Fintype.sum_prod_type, ite_and, mul_ite]

private theorem slice_identity_iff_mul {r : Nat} (A B C : Fin r -> Mat3) (X : Mat3) :
    (∀ b c : Coord9, matrixDual (tensorASlice b c) X =
      ∑ t : Fin r, matrixDual (A t) X * B t b.1 b.2 * C t c.1 c.2) ↔
    ∀ Y : Mat3, X * Y = bilinearAlgorithm A B C X Y := by
  constructor
  · intro h Y
    ext i k
    rw [mul_contract_slices X Y (i, k)]
    simp_rw [h]
    change (∑ b : Coord9, Y b.1 b.2 *
        ∑ t : Fin r, matrixDual (A t) X * B t b.1 b.2 * C t i k) =
      (∑ t : Fin r, (matrixDual (A t) X *
        (∑ b : Coord9, B t b.1 b.2 * Y b.1 b.2)) • C t) i k
    simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
      Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro t _
    apply Finset.sum_congr rfl
    intro b _
    ring
  · intro h b c
    have hc := congrArg (fun M : Mat3 => M c.1 c.2)
      (h (Matrix.single b.1 b.2 1))
    rwa [← slice_pairing_single, algorithm_single] at hc

private theorem pairing_residual {r : Nat} (A B C : Fin r -> Mat3)
    (X : Mat3) (b c : Coord9) :
    matrixDual (tensorASlice b c +
      ∑ t : Fin r, (B t b.1 b.2 * C t c.1 c.2) • A t) X =
      matrixDual (tensorASlice b c) X +
        ∑ t : Fin r, matrixDual (A t) X * B t b.1 b.2 * C t c.1 c.2 := by
  simp only [map_add, map_sum, map_smul, LinearMap.add_apply,
    LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro t _
  ring

/-- Same coefficient triples, equivalent identities: quotienting the A-slot
is precisely restricting X to W's annihilator, with all Y and full output. -/
theorem quotient_identity_iff_restricted_mul (W : Submodule F2 Mat3)
    {r : Nat} (A B C : Fin r -> Mat3) :
    (∀ b c : Coord9, tensorASlice b c +
      (∑ t : Fin r, (B t b.1 b.2 * C t c.1 c.2) • A t) ∈ W) ↔
    (∀ X : inputAnnihilator W, ∀ Y : Mat3,
      (X : Mat3) * Y = bilinearAlgorithm A B C X Y) := by
  constructor
  · intro h X
    apply (slice_identity_iff_mul A B C X).mp
    intro b c
    have hz := (mem_iff_annihilator W _).mp (h b c) X X.property
    rwa [pairing_residual, add_eq_zero_iff_eq_neg, CharTwo.neg_eq] at hz
  · intro h b c
    apply (mem_iff_annihilator W _).mpr
    intro X hX
    have he := (slice_identity_iff_mul A B C X).mpr (h ⟨X, hX⟩) b c
    rw [pairing_residual, he, CharTwo.add_self_eq_zero]

/-- An intrinsic bilinear algorithm on the restricted first-input space.
Both input forms are arbitrary linear maps. C is the actual output matrix. -/
structure RestrictedDecomp (W : Submodule F2 Mat3) (r : Nat) where
  left : Fin r -> Module.Dual F2 (inputAnnihilator W)
  right : Fin r -> Module.Dual F2 Mat3
  output : Fin r -> Mat3
  identity : ∀ X : inputAnnihilator W, ∀ Y : Mat3,
    (X : Mat3) * Y = ∑ t : Fin r, (left t X * right t Y) • output t

/-- Restriction preserves the number of summands, including zero summands. -/
def toRestricted {W : Submodule F2 Mat3} {r : Nat}
    (D : QuotientTensorDecomp W r) : RestrictedDecomp W r where
  left t := restrictCoefficient W (D.A t)
  right t := matrixDual (D.B t)
  output := D.C
  identity := (quotient_identity_iff_restricted_mul W D.A D.B D.C).mp D.quotient_identity

/-- Every intrinsic restricted algorithm lifts to quotient coefficients.
Mathlib's extension/surjectivity theorem supplies its first coefficient matrices. -/
noncomputable def toQuotient {W : Submodule F2 Mat3} {r : Nat}
    (D : RestrictedDecomp W r) : QuotientTensorDecomp W r where
  A t := (restrictCoefficient_surjective W (D.left t)).choose
  B t := matrixDual.symm (D.right t)
  C := D.output
  quotient_identity := by
    apply (quotient_identity_iff_restricted_mul W _ _ _).mpr
    intro X Y
    convert D.identity X Y using 1
    apply Finset.sum_congr rfl
    intro t _
    congr 1
    change matrixDual ((restrictCoefficient_surjective W (D.left t)).choose) X *
      matrixDual (matrixDual.symm (D.right t)) Y = D.left t X * D.right t Y
    rw [matrixDual.apply_symm_apply]
    have h := LinearMap.congr_fun
      (restrictCoefficient_surjective W (D.left t)).choose_spec X
    rw [restrictCoefficient_apply] at h
    rw [h]

/-- Arbitrary-W, length-preserving equivalence of decomposition existence. -/
theorem nonempty_quotient_iff_restricted (W : Submodule F2 Mat3) (r : Nat) :
    Nonempty (QuotientTensorDecomp W r) ↔ Nonempty (RestrictedDecomp W r) :=
  ⟨fun ⟨D⟩ => ⟨toRestricted D⟩, fun ⟨D⟩ => ⟨toQuotient D⟩⟩

/-- Rank upper bounds agree as well; the same witness length works both ways. -/
theorem rankAtMost_iff_restricted (W : Submodule F2 Mat3) (n : Nat) :
    (∃ r : Nat, r ≤ n ∧ Nonempty (QuotientTensorDecomp W r)) ↔
      ∃ r : Nat, r ≤ n ∧ Nonempty (RestrictedDecomp W r) := by
  simp_rw [nonempty_quotient_iff_restricted]

/-- Intrinsic restricted bilinear rank lower bounds equal quotient rank bounds. -/
theorem quotientRankAtLeast_iff_restricted (W : Submodule F2 Mat3) (n : Nat) :
    QuotientRankAtLeast W n ↔ ∀ r : Nat, RestrictedDecomp W r -> n ≤ r := by
  constructor
  · intro h r D
    by_contra hn
    exact (h r (by omega)).false (toQuotient D)
  · intro h r hr
    exact ⟨fun D => (Nat.not_le_of_gt hr) (h r (toRestricted D))⟩

/-- Operational rank statement with arbitrary first and second linear forms. -/
theorem quotientRankAtLeast_iff_restricted_mul (W : Submodule F2 Mat3) (n : Nat) :
    QuotientRankAtLeast W n ↔
      ∀ (r : Nat) (left : Fin r -> Module.Dual F2 (inputAnnihilator W))
        (right : Fin r -> Module.Dual F2 Mat3) (output : Fin r -> Mat3),
        (∀ X : inputAnnihilator W, ∀ Y : Mat3,
          (X : Mat3) * Y = ∑ t : Fin r, (left t X * right t Y) • output t) -> n ≤ r := by
  rw [quotientRankAtLeast_iff_restricted]
  exact ⟨fun h r left right output hi => h r ⟨left, right, output, hi⟩,
    fun h r D => h r D.left D.right D.output D.identity⟩

end QiushiMatmul.QuotientRestriction
