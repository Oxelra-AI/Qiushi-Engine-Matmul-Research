import QiushiMatmul
import QiushiFrozenWangData
import QiushiCertifiedTransport

/-!
Adapters for a partial rank-soundness registry of frozen representatives.
No classification, global table soundness, or numeric L0 equality is assumed.
-/

namespace QiushiMatmul.FrozenRegistry

theorem span_le_of_checked (target source : List Nat)
    (h : ∀ c ∈ target, spanContainsCode source c = true) :
    spanCodes target ≤ spanCodes source := by
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact spanContainsCode_implies_mem_spanCodes source c (h c hc)

theorem span_eq_of_checked (target source : List Nat)
    (h : ∀ c ∈ target, spanContainsCode source c = true)
    (hback : ∀ c ∈ source, spanContainsCode target c = true) :
    spanCodes target = spanCodes source :=
  le_antisymm (span_le_of_checked target source h) (span_le_of_checked source target hback)

theorem bind_exact (target source : List Nat) {wanted known : Nat}
    (h : QuotientRankAtLeast (spanCodes source) known)
    (hforward : ∀ c ∈ target, spanContainsCode source c = true)
    (hback : ∀ c ∈ source, spanContainsCode target c = true)
    (hle : wanted ≤ known) : QuotientRankAtLeast (spanCodes target) wanted := by
  rw [span_eq_of_checked target source hforward hback]
  exact quotientRankAtLeast_weaken h hle

theorem bind_contained (target source : List Nat) {wanted known : Nat}
    (h : QuotientRankAtLeast (spanCodes source) known)
    (hforward : ∀ c ∈ target, spanContainsCode source c = true)
    (hle : wanted ≤ known) : QuotientRankAtLeast (spanCodes target) wanted :=
  quotientRankAtLeast_weaken
    (quotientRankAtLeast_mono (span_le_of_checked target source hforward) h) hle

/-- Reverse exact orbit transport; a one-way containment does not suffice. -/
theorem bind_orbit (table : FrozenOrbitTable) (i : Fin 496)
    {W : Submodule F2 Mat3} {known : Nat}
    (horbit : table.OrbitImage i W) (h : QuotientRankAtLeast W known)
    (hle : table.lower i ≤ known) :
    QuotientRankAtLeast (spanCodes (table.basis i)) (table.lower i) := by
  obtain ⟨P, Q, ⟨hP⟩, ⟨hQ⟩, flip, hW⟩ := horbit
  let _ := hP
  let _ := hQ
  rw [hW] at h
  have hback := quotientRankAtLeast_action_iff.mpr h
  cases flip with
  | false => exact quotientRankAtLeast_weaken hback hle
  | true =>
      exact quotientRankAtLeast_weaken
        (quotientRankAtLeast_transpose_iff.mpr hback) hle

/-- The zero-quotient representation recovers the original entrywise identity. -/
def entryDecompOfZeroQuotient {r : Nat}
    (D : QuotientTensorDecomp (spanCodes []) r) : TensorEntryDecomp r where
  A := D.A
  B := D.B
  C := D.C
  entry_identity := by
    intro a b c
    have h := D.quotient_identity b c
    have hzero : tensorASlice b c +
        (∑ t : Fin r, (D.B t b.1 b.2 * D.C t c.1 c.2) • D.A t) = 0 := by
      simpa [spanCodes] using h
    have he := congrFun (congrFun hzero a.1) a.2
    have hneg (x : F2) : -x = x := by revert x; decide
    have hsum : tensorEntry a b c +
        (∑ t : Fin r, D.A t a.1 a.2 * D.B t b.1 b.2 * D.C t c.1 c.2) = 0 := by
      simpa [tensorASlice, Matrix.sum_apply, Matrix.smul_apply,
        mul_comm, mul_left_comm, mul_assoc] using he
    simpa only [hneg] using (add_eq_zero_iff_eq_neg.mp hsum)

theorem zero_quotient_bound : QuotientRankAtLeast (spanCodes []) 21 := by
  intro r hr
  constructor
  intro D
  have h := rank_ge_21 r (entryDecompOfZeroQuotient D)
  omega

/-- An explicit column permutation connects the two stored bases for orbit 416. -/
theorem orbit416 : frozenWangTable.OrbitImage 416 (spanCodes [272, 4, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 416
    [(272, 96), (4, 1), (1, 2)]
    (codeMat 273) (codeMat 140) (codeMat 98) false
    (by decide) (by decide) (by decide)
    (by rw [show frozenWangTable.basis 416 = [96, 2, 1] by decide]; decide)
    (by rw [show frozenWangTable.basis 416 = [96, 2, 1] by decide]; decide)

theorem bound416 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 416))
      (frozenWangTable.lower 416) :=
  bind_orbit frozenWangTable 416 orbit416 step113_orbit416_lb17 (by decide)

end QiushiMatmul.FrozenRegistry
