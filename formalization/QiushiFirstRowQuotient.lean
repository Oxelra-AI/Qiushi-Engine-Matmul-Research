import QiushiMatmulFinitePremises

/-!
# The first-row quotient is rectangular matrix multiplication

The A-slot quotient by the actual `spanCodes [4,2,1]` is the lower two rows.
B retains all nine coordinates. C initially retains nine coordinates too;
its unused first row can be projected away and zero-padded back without
changing the existence of an exact decomposition of any given length.
-/

open Matrix BigOperators

namespace QiushiMatmul

abbrev Mat23 := Matrix (Fin 2) I3 F2
abbrev Coord23 := Fin 2 × I3

/-- Delete row zero, without changing the column order. -/
def lowerRows : Mat3 →ₗ[F2] Mat23 where
  toFun M i j := M i.succ j
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem lowerRows_apply (M : Mat3) (i : Fin 2) (j : I3) :
    lowerRows M i j = M i.succ j := rfl

/-- Include a rectangular matrix with a zero first row. -/
def padLowerRows : Mat23 →ₗ[F2] Mat3 where
  toFun M := Fin.cases 0 M
  map_add' M N := by ext i j; refine Fin.cases ?_ (fun k => ?_) i <;> rfl
  map_smul' c M := by
    ext i j
    change (Fin.cases (motive := fun _ => I3 → F2) 0 (c • M) i) j =
      c • (Fin.cases (motive := fun _ => I3 → F2) 0 M i) j
    refine Fin.cases ?_ (fun k => ?_) i
    · change (0 : F2) = c • (0 : F2)
      simp
    · rfl

@[simp] theorem padLowerRows_zero (M : Mat23) (j : I3) :
    padLowerRows M 0 j = 0 := rfl

@[simp] theorem padLowerRows_succ (M : Mat23) (i : Fin 2) (j : I3) :
    padLowerRows M i.succ j = M i j := rfl

@[simp] theorem lowerRows_padLowerRows (M : Mat23) :
    lowerRows (padLowerRows M) = M := rfl

/-- This checks the report's code convention, rather than assuming a row span. -/
theorem firstRowFamily_eq_ker_lowerRows : firstRowFamily = LinearMap.ker lowerRows := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro M ⟨n, hn, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with rfl | rfl | rfl <;>
      (change lowerRows (codeMat _) = 0
       ext i j
       fin_cases i <;> fin_cases j <;> decide)
  · intro M hM
    have hzero : ∀ i : Fin 2, ∀ j : I3, M i.succ j = 0 := by
      intro i j
      exact congrArg (fun N : Mat23 => N i j) hM
    have h1 := hzero 0
    have h2 := hzero 1
    have hcode (n : Nat) (hn : n ∈ [4,2,1]) : codeMat n ∈ firstRowFamily :=
      Submodule.subset_span ⟨n, hn, rfl⟩
    have hrepr : M = M 0 0 • codeMat 1 + M 0 1 • codeMat 2 + M 0 2 • codeMat 4 := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        norm_num [codeMat, Nat.testBit, Nat.shiftRight_eq_div_pow,
          Matrix.add_apply, Matrix.smul_apply] <;>
        first | rfl | exact h1 _ | exact h2 _
    rw [hrepr]
    exact firstRowFamily.add_mem
      (firstRowFamily.add_mem (firstRowFamily.smul_mem _ (hcode 1 (by simp)))
        (firstRowFamily.smul_mem _ (hcode 2 (by simp))))
      (firstRowFamily.smul_mem _ (hcode 4 (by simp)))

theorem mem_firstRowFamily_iff (M : Mat3) :
    M ∈ firstRowFamily ↔ lowerRows M = 0 := by
  rw [firstRowFamily_eq_ker_lowerRows, LinearMap.mem_ker]

/-- The genuine first-coordinate quotient linear equivalence. -/
noncomputable def firstRowQuotientEquiv : (Mat3 ⧸ firstRowFamily) ≃ₗ[F2] Mat23 :=
  (Submodule.quotEquivOfEq _ _ firstRowFamily_eq_ker_lowerRows).trans
    (lowerRows.quotKerEquivOfSurjective (fun M => ⟨padLowerRows M, rfl⟩))

@[simp] theorem firstRowQuotientEquiv_mk (M : Mat3) :
    firstRowQuotientEquiv (Submodule.Quotient.mk M) = lowerRows M := by
  simp only [firstRowQuotientEquiv, LinearEquiv.trans_apply, Submodule.quotEquivOfEq_mk]
  rfl

/-- Coefficients for `(2 x 3) * (3 x 3)`, with a `(2 x 3)` output. -/
def rectTensorEntry (a : Coord23) (b : Coord9) (c : Coord23) : F2 :=
  if b.1 = a.2 ∧ c.1 = a.1 ∧ c.2 = b.2 then 1 else 0

/-- Independent identification with ordinary rectangular matrix multiplication. -/
theorem rectTensorEntry_contract (X : Mat23) (Y : Mat3) (i : Fin 2) (k : I3) :
    (∑ a : Coord23, ∑ b : Coord9,
      X a.1 a.2 * Y b.1 b.2 * rectTensorEntry a b (i, k)) = (X * Y) i k := by
  simp [rectTensorEntry, Fintype.sum_prod_type, Matrix.mul_apply, ite_and, mul_ite]

/-- Quotient slices at the six active output coordinates are rectangular slices. -/
theorem firstRowQuotientEquiv_slice (b : Coord9) (c : Coord23) :
    firstRowQuotientEquiv (Submodule.Quotient.mk (tensorASlice b (c.1.succ, c.2))) =
      fun i j => rectTensorEntry (i,j) b c := by
  rw [firstRowQuotientEquiv_mk]
  ext i j
  simp [tensorASlice, tensorEntry, rectTensorEntry]

/-- The three first-row output coordinates vanish only after the A-quotient. -/
theorem firstRowQuotientEquiv_slice_zero (b : Coord9) (k : I3) :
    firstRowQuotientEquiv (Submodule.Quotient.mk (tensorASlice b (0,k))) = 0 := by
  rw [firstRowQuotientEquiv_mk]
  ext i j
  simp [tensorASlice, tensorEntry, eq_comm]

structure RectTensorDecomp (r : Nat) where
  A : Fin r → Mat23
  B : Fin r → Mat3
  C : Fin r → Mat23
  entry_identity : ∀ (a : Coord23) (b : Coord9) (c : Coord23),
    rectTensorEntry a b c = ∑ t : Fin r, A t a.1 a.2 * B t b.1 b.2 * C t c.1 c.2

/-- Restrict both A and C; B remains a full 3 x 3 matrix. -/
def QuotientTensorDecomp.toRect {r : Nat} (D : QuotientTensorDecomp firstRowFamily r) :
    RectTensorDecomp r where
  A t := lowerRows (D.A t)
  B := D.B
  C t := lowerRows (D.C t)
  entry_identity := by
    intro a b c
    have h := (mem_firstRowFamily_iff _).mp (D.quotient_identity b (c.1.succ, c.2))
    have he := congrArg (fun M : Mat23 => M a.1 a.2) h
    simp only [map_add, map_sum, map_smul, Matrix.add_apply, Matrix.sum_apply,
      Matrix.smul_apply, Matrix.zero_apply, smul_eq_mul] at he
    have hentry : lowerRows (tensorASlice b (c.1.succ,c.2)) a.1 a.2 =
        rectTensorEntry a b c := by
      simp [tensorASlice, tensorEntry, rectTensorEntry]
    rw [hentry] at he
    have heq := eq_neg_of_add_eq_zero_left he
    simpa [CharTwo.neg_eq, mul_comm, mul_left_comm, mul_assoc] using heq

/-- Zero-padding A and C proves that deleting unused output coordinates adds no rank. -/
def RectTensorDecomp.toFirstRowQuotient {r : Nat} (D : RectTensorDecomp r) :
    QuotientTensorDecomp firstRowFamily r where
  A t := padLowerRows (D.A t)
  B := D.B
  C t := padLowerRows (D.C t)
  quotient_identity := by
    intro b c
    apply (mem_firstRowFamily_iff _).mpr
    ext i j
    rcases c with ⟨ci, ck⟩
    refine Fin.cases ?_ (fun k => ?_) ci
    · simp [tensorASlice, tensorEntry, eq_comm]
    · have h := D.entry_identity (i,j) b (k,ck)
      simpa [tensorASlice, tensorEntry, rectTensorEntry,
        Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
        mul_comm, mul_left_comm, mul_assoc] using
        (show rectTensorEntry (i,j) b (k,ck) +
          (∑ t : Fin r, D.A t i j * D.B t b.1 b.2 * D.C t k ck) = 0 by
            rw [h, CharTwo.add_self_eq_zero])

theorem firstRow_quotient_decomp_iff (r : Nat) :
    Nonempty (QuotientTensorDecomp firstRowFamily r) ↔ Nonempty (RectTensorDecomp r) :=
  ⟨fun ⟨D⟩ => ⟨D.toRect⟩, fun ⟨D⟩ => ⟨D.toFirstRowQuotient⟩⟩

/-- Every lower bound, hence the minimum decomposition length, is preserved. -/
theorem firstRow_quotient_rankAtLeast_iff (n : Nat) :
    QuotientRankAtLeast firstRowFamily n ↔
      ∀ r : Nat, RectTensorDecomp r → n ≤ r := by
  constructor
  · intro h r D
    by_contra hnr
    exact (h r (Nat.lt_of_not_ge hnr)).false D.toFirstRowQuotient
  · intro h r hr
    exact ⟨fun D => Nat.not_le_of_gt hr (h r D.toRect)⟩

@[simp] theorem RectTensorDecomp.toFirstRowQuotient_toRect {r : Nat}
    (D : RectTensorDecomp r) : D.toFirstRowQuotient.toRect = D := by
  cases D
  rfl

/-- Fix the redundant A-lifts and remove the unused C coordinates. Arbitrary
quotient records need not be in bijection: both freedoms are real. -/
def NormalizedFirstRowDecomp (r : Nat) :=
  { D : QuotientTensorDecomp firstRowFamily r // ∀ t : Fin r,
    padLowerRows (lowerRows (D.A t)) = D.A t ∧
    padLowerRows (lowerRows (D.C t)) = D.C t }

/-- An actual bijection of exact length-r decomposition records in normal form. -/
def normalizedFirstRowDecompEquiv (r : Nat) :
    NormalizedFirstRowDecomp r ≃ RectTensorDecomp r where
  toFun D := D.val.toRect
  invFun D := ⟨D.toFirstRowQuotient, fun _ => ⟨rfl, rfl⟩⟩
  left_inv D := by
    apply Subtype.ext
    have hA : (fun t => padLowerRows (lowerRows (D.val.A t))) = D.val.A :=
      funext (fun t => (D.property t).1)
    have hC : (fun t => padLowerRows (lowerRows (D.val.C t))) = D.val.C :=
      funext (fun t => (D.property t).2)
    rcases D with ⟨⟨A,B,C,h⟩, hn⟩
    dsimp [QuotientTensorDecomp.toRect, RectTensorDecomp.toFirstRowQuotient] at hA hC ⊢
    congr
  right_inv := RectTensorDecomp.toFirstRowQuotient_toRect

section TensorProduct

open scoped TensorProduct

/-- The output support, inside the original nine-dimensional C-slot. -/
abbrev FirstRowOutputSupport := LinearMap.range padLowerRows

noncomputable def firstRowOutputEquiv : FirstRowOutputSupport ≃ₗ[F2] Mat23 :=
  (LinearEquiv.ofInjective padLowerRows
    (Function.LeftInverse.injective lowerRows_padLowerRows)).symm

@[simp] theorem firstRowOutputEquiv_symm_coe (M : Mat23) :
    ((firstRowOutputEquiv.symm M : FirstRowOutputSupport) : Mat3) = padLowerRows M := rfl

private def unit9 (c : Coord9) : Mat3 := Matrix.single c.1 c.2 1
private def unit23 (c : Coord23) : Mat23 := Matrix.single c.1 c.2 1

private theorem padLowerRows_unit23 (c : Coord23) :
    padLowerRows (unit23 c) = unit9 (c.1.succ,c.2) := by
  ext i j
  refine Fin.cases ?_ (fun k => ?_) i
  · simp [unit9, eq_comm]
  · simp [unit9, unit23, Matrix.single_apply]

/-- The full tensor built from the project's canonical A-slices. -/
def fullMatmulTensor : Mat3 ⊗[F2] (Mat3 ⊗[F2] Mat3) :=
  ∑ b : Coord9, ∑ c : Coord9,
    tensorASlice b c ⊗ₜ[F2] (unit9 b ⊗ₜ[F2] unit9 c)

/-- Apply the quotient only to the first coordinate. B and C are unchanged. -/
def firstRowQuotientTensor : (Mat3 ⧸ firstRowFamily) ⊗[F2] (Mat3 ⊗[F2] Mat3) :=
  TensorProduct.map firstRowFamily.mkQ (LinearMap.id :
    (Mat3 ⊗[F2] Mat3) →ₗ[F2] (Mat3 ⊗[F2] Mat3)) fullMatmulTensor

/-- The same quotient tensor, represented on its active C support. -/
noncomputable def firstRowSupportedTensor :
    (Mat3 ⧸ firstRowFamily) ⊗[F2] (Mat3 ⊗[F2] FirstRowOutputSupport) :=
  ∑ b : Coord9, ∑ c : Coord23,
    firstRowFamily.mkQ (tensorASlice b (c.1.succ,c.2)) ⊗ₜ[F2]
      (unit9 b ⊗ₜ[F2] firstRowOutputEquiv.symm (unit23 c))

def rectMatmulTensor : Mat23 ⊗[F2] (Mat3 ⊗[F2] Mat23) :=
  ∑ b : Coord9, ∑ c : Coord23,
    (fun i j => rectTensorEntry (i,j) b c) ⊗ₜ[F2] (unit9 b ⊗ₜ[F2] unit23 c)

/-- Slotwise linear equivalence after restricting to the actual output support. -/
noncomputable def firstRowTensorEquiv :
    ((Mat3 ⧸ firstRowFamily) ⊗[F2] (Mat3 ⊗[F2] FirstRowOutputSupport)) ≃ₗ[F2]
      (Mat23 ⊗[F2] (Mat3 ⊗[F2] Mat23)) :=
  TensorProduct.congr firstRowQuotientEquiv
    (TensorProduct.congr (LinearEquiv.refl F2 Mat3) firstRowOutputEquiv)

theorem firstRowTensorEquiv_tensor :
    firstRowTensorEquiv firstRowSupportedTensor = rectMatmulTensor := by
  simp only [firstRowTensorEquiv, firstRowSupportedTensor, rectMatmulTensor,
    map_sum, TensorProduct.congr_tmul, LinearEquiv.refl_apply,
    LinearEquiv.apply_symm_apply]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro c _
  rw [show firstRowQuotientEquiv (firstRowFamily.mkQ
    (tensorASlice b (c.1.succ,c.2))) = fun i j => rectTensorEntry (i,j) b c from
      firstRowQuotientEquiv_slice b c]

/-- No output restriction is hidden in `firstRowQuotientTensor`: inclusion of
the supported tensor is exactly the first-coordinate quotient of the full tensor. -/
theorem firstRowSupportedTensor_inclusion :
    TensorProduct.map (LinearMap.id : (Mat3 ⧸ firstRowFamily) →ₗ[F2] _)
      (TensorProduct.map (LinearMap.id : Mat3 →ₗ[F2] Mat3)
        (LinearMap.range padLowerRows).subtype) firstRowSupportedTensor =
      firstRowQuotientTensor := by
  simp only [firstRowSupportedTensor, firstRowQuotientTensor, fullMatmulTensor,
    map_sum, TensorProduct.map_tmul, LinearMap.id_apply, Submodule.subtype_apply,
    firstRowOutputEquiv_symm_coe, padLowerRows_unit23]
  apply Finset.sum_congr rfl
  intro b _
  have hz (k : I3) : firstRowFamily.mkQ (tensorASlice b (0,k)) = 0 := by
    apply firstRowQuotientEquiv.injective
    simpa using firstRowQuotientEquiv_slice_zero b k
  simp only [Fintype.sum_prod_type]
  conv_rhs => rw [Fin.sum_univ_succ]
  simp only [hz, TensorProduct.zero_tmul, Finset.sum_const_zero, zero_add]

end TensorProduct

end QiushiMatmul
