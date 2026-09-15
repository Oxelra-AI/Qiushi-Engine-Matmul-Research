import QiushiDefs

/-!
Coordinate tensor decompositions are exactly bilinear algorithms for `X * Y`.
The third coefficient matrix is the output matrix, without a transpose.
-/

open Matrix BigOperators

namespace QiushiMatmul

/-- Evaluate arbitrary coefficient triples as a bilinear matrix algorithm. -/
def bilinearAlgorithm {r : Nat} (A B C : Fin r -> Mat3) (X Y : Mat3) : Mat3 :=
  ∑ t : Fin r,
    ((∑ a : Coord9, A t a.1 a.2 * X a.1 a.2) *
      (∑ b : Coord9, B t b.1 b.2 * Y b.1 b.2)) • C t

/-- Contracting the canonical coefficients gives ordinary matrix multiplication. -/
theorem tensorEntry_contract (X Y : Mat3) (i k : I3) :
    (∑ a : Coord9, ∑ b : Coord9,
      X a.1 a.2 * Y b.1 b.2 * tensorEntry a b (i, k)) = (X * Y) i k := by
  simp [tensorEntry, Fintype.sum_prod_type, Matrix.mul_apply, ite_and, mul_ite]

private theorem bilinearAlgorithm_apply {r : Nat} (A B C : Fin r -> Mat3)
    (X Y : Mat3) (i k : I3) :
    bilinearAlgorithm A B C X Y i k =
      ∑ a : Coord9, ∑ b : Coord9,
        X a.1 a.2 * Y b.1 b.2 *
          (∑ t : Fin r, A t a.1 a.2 * B t b.1 b.2 * C t i k) := by
  simp only [bilinearAlgorithm, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  simp only [Finset.sum_mul]
  simp only [Finset.mul_sum]
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro t _
  ac_rfl

private theorem coefficient_sum_single (A : Mat3) (a : Coord9) :
    (∑ d : Coord9, A d.1 d.2 * (Matrix.single a.1 a.2 (1 : F2)) d.1 d.2) =
      A a.1 a.2 := by
  simp [Fintype.sum_prod_type, Matrix.single_apply, ite_and, mul_ite]

/-- Matrix units recover exactly the project's `tensorEntry` index convention. -/
theorem tensorEntry_eq_single_mul (a b c : Coord9) :
    tensorEntry a b c =
      ((Matrix.single a.1 a.2 (1 : F2) * Matrix.single b.1 b.2 1) : Mat3) c.1 c.2 := by
  simp [Matrix.mul_apply, Matrix.single_apply, tensorEntry, ite_and, mul_ite, eq_comm]
  split_ifs <;> rfl

/-- The 729 coefficient identities are equivalent to correctness on all inputs. -/
theorem tensorEntry_identity_iff_bilinearAlgorithm {r : Nat}
    (A B C : Fin r -> Mat3) :
    (∀ a b c : Coord9,
      tensorEntry a b c = ∑ t : Fin r, A t a.1 a.2 * B t b.1 b.2 * C t c.1 c.2) ↔
    (∀ X Y : Mat3, X * Y = bilinearAlgorithm A B C X Y) := by
  constructor
  · intro h X Y
    apply Matrix.ext
    intro i k
    rw [← tensorEntry_contract X Y i k, bilinearAlgorithm_apply]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    rw [h]
  · intro h a b c
    have heq := congrArg (fun M : Mat3 => M c.1 c.2)
      (h (Matrix.single a.1 a.2 1) (Matrix.single b.1 b.2 1))
    simpa only [bilinearAlgorithm, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
      coefficient_sum_single, ← tensorEntry_eq_single_mul] using heq

/-- Every stored tensor decomposition computes actual matrix products. -/
theorem TensorEntryDecomp.mul_eq {r : Nat} (D : TensorEntryDecomp r) (X Y : Mat3) :
    X * Y = ∑ t : Fin r, (leftForm D t X * rightForm D t Y) • D.C t := by
  have h := (tensorEntry_identity_iff_bilinearAlgorithm D.A D.B D.C).mp
    D.entry_identity X Y
  simpa only [bilinearAlgorithm, leftForm, rightForm, mul_comm] using h

/-- Build the existing decomposition record from an all-input bilinear algorithm. -/
def tensorEntryDecompOfBilinear {r : Nat} (A B C : Fin r -> Mat3)
    (h : ∀ X Y : Mat3, X * Y = bilinearAlgorithm A B C X Y) : TensorEntryDecomp r where
  A := A
  B := B
  C := C
  entry_identity := (tensorEntry_identity_iff_bilinearAlgorithm A B C).mpr h

/-- Existence of a length-r coordinate decomposition is the operational specification. -/
theorem nonempty_tensorEntryDecomp_iff_bilinearAlgorithm (r : Nat) :
    Nonempty (TensorEntryDecomp r) ↔
      ∃ A B C : Fin r -> Mat3, ∀ X Y : Mat3, X * Y = bilinearAlgorithm A B C X Y := by
  constructor
  · rintro ⟨D⟩
    exact ⟨D.A, D.B, D.C,
      (tensorEntry_identity_iff_bilinearAlgorithm D.A D.B D.C).mp D.entry_identity⟩
  · rintro ⟨A, B, C, h⟩
    exact ⟨tensorEntryDecompOfBilinear A B C h⟩

/-- The existing rank lower-bound predicate applies to actual bilinear algorithms. -/
theorem rankAtLeast_iff_bilinearAlgorithm (n : Nat) :
    RankAtLeast n ↔ ∀ (r : Nat) (A B C : Fin r -> Mat3),
      (∀ X Y : Mat3, X * Y = bilinearAlgorithm A B C X Y) -> n ≤ r := by
  constructor
  · intro h r A B C hAlg
    exact h r (tensorEntryDecompOfBilinear A B C hAlg)
  · intro h r D
    exact h r D.A D.B D.C
      ((tensorEntry_identity_iff_bilinearAlgorithm D.A D.B D.C).mp D.entry_identity)

end QiushiMatmul
