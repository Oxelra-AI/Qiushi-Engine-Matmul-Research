import QiushiWeightedCover

/-!
# Dimension-independent direct matrix coverage for occupation certificates

Instead of quotient-label classifiers (which grow in complexity with each
quotient dimension), we check the finite coverage condition directly on all
512 elements of `Mat3` over `𝔽₂`.  For a direct certificate with sources
`sourceU i ⊇ W` and row multipliers `λ_i`, the condition

  `∀ M : Mat3, λ₀ ≤ ∑ᵢ (if M ∈ sourceU i then λ_i else 0)`

implies term-level coverage for any quotient decomposition, because each
`D.A t` is an element of `Mat3`.  A second theorem lets generated proof files
use a computable coverage predicate together with a soundness implication into
`sourceU`; this avoids asking Lean to synthesize decidability for abstract
submodule membership during the 512-matrix finite check.
-/

set_option maxHeartbeats 8000000
open BigOperators Finset Classical
namespace QiushiMatmul

/-- Direct-coverage occupation contradiction using membership in the source
submodules themselves. -/
theorem direct_coverage_quotient_decomp_false
    {m r : ℕ}
    {W : Submodule F2 Mat3}
    (sourceU : Fin m → Submodule F2 Mat3)
    (sourceLb : Fin m → ℕ)
    (lambda : Fin m → ℕ) (lambda0 target : ℕ)
    (hWU : ∀ i : Fin m, W ≤ sourceU i)
    (hSource : ∀ i : Fin m, QuotientRankAtLeast (sourceU i) (sourceLb i))
    (hLambda : lambda0 ≤ ∑ i : Fin m, lambda i)
    (hMatCov : ∀ M : Mat3, lambda0 ≤ ∑ i : Fin m,
      if M ∈ sourceU i then lambda i else 0)
    (hrt : r ≤ target)
    (hCert : ((∑ i : Fin m, lambda i) - lambda0) * target <
        ∑ i : Fin m, lambda i * sourceLb i)
    (D : QuotientTensorDecomp W r) :
    False := by
  classical
  by_cases hAllLe : ∀ i : Fin m, sourceLb i ≤ r
  · have hTermCov : ∀ t : Fin r,
        lambda0 ≤ ∑ i : Fin m,
          if t ∈ killSet D (sourceU i) then lambda i else 0 := by
      intro t
      have hMat := hMatCov (D.A t)
      convert hMat using 1
      apply Finset.sum_congr rfl
      intro i _
      congr 1
      simp only [killSet, Finset.mem_filter, Finset.mem_univ, true_and]
    have hRowsAdd : ∀ i : Fin m,
        (killSet D (sourceU i)).card + sourceLb i ≤ r := by
      intro i
      have hk : (killSet D (sourceU i)).card ≤ r - sourceLb i :=
        occupation_inequality (hWU i) D (hSource i) (hAllLe i)
      calc (killSet D (sourceU i)).card + sourceLb i
          ≤ (r - sourceLb i) + sourceLb i :=
            Nat.add_le_add_right hk (sourceLb i)
        _ = r := Nat.sub_add_cancel (hAllLe i)
    exact weighted_cover_infeasible_from_term_coverage
      (fun i => killSet D (sourceU i)) sourceLb lambda lambda0 target
      hLambda hTermCov hRowsAdd hrt hCert
  · push Not at hAllLe
    rcases hAllLe with ⟨i, hi⟩
    exact quotient_bound_exceeds_length (hWU i) D (hSource i) hi

/-- Direct-coverage occupation contradiction using a computable coverage
predicate.  The predicate `cover i M` may be any decidable/generated condition;
it only has to imply actual membership in `sourceU i`.  This is the practical
interface for generated modules, where coverage is checked by evaluating linear
functional equations rather than by deciding arbitrary submodule membership. -/
theorem direct_coverage_quotient_decomp_false_of_cover
    {m r : ℕ}
    {W : Submodule F2 Mat3}
    (sourceU : Fin m → Submodule F2 Mat3)
    (sourceLb : Fin m → ℕ)
    (lambda : Fin m → ℕ) (lambda0 target : ℕ)
    (cover : Fin m → Mat3 → Prop)
    (hWU : ∀ i : Fin m, W ≤ sourceU i)
    (hSource : ∀ i : Fin m, QuotientRankAtLeast (sourceU i) (sourceLb i))
    (hLambda : lambda0 ≤ ∑ i : Fin m, lambda i)
    (hCoverSound : ∀ (i : Fin m) (M : Mat3), cover i M → M ∈ sourceU i)
    (hMatCov : ∀ M : Mat3, lambda0 ≤ ∑ i : Fin m,
      if cover i M then lambda i else 0)
    (hrt : r ≤ target)
    (hCert : ((∑ i : Fin m, lambda i) - lambda0) * target <
        ∑ i : Fin m, lambda i * sourceLb i)
    (D : QuotientTensorDecomp W r) :
    False := by
  classical
  by_cases hAllLe : ∀ i : Fin m, sourceLb i ≤ r
  · have hTermCov : ∀ t : Fin r,
        lambda0 ≤ ∑ i : Fin m,
          if t ∈ killSet D (sourceU i) then lambda i else 0 := by
      intro t
      have hMat := hMatCov (D.A t)
      refine le_trans hMat ?_
      apply Finset.sum_le_sum
      intro i _
      by_cases hc : cover i (D.A t)
      · have ht : t ∈ killSet D (sourceU i) := by
          simp only [killSet, Finset.mem_filter, Finset.mem_univ, true_and]
          exact hCoverSound i (D.A t) hc
        simp [hc, ht]
      · simp [hc]
    have hRowsAdd : ∀ i : Fin m,
        (killSet D (sourceU i)).card + sourceLb i ≤ r := by
      intro i
      have hk : (killSet D (sourceU i)).card ≤ r - sourceLb i :=
        occupation_inequality (hWU i) D (hSource i) (hAllLe i)
      calc (killSet D (sourceU i)).card + sourceLb i
          ≤ (r - sourceLb i) + sourceLb i :=
            Nat.add_le_add_right hk (sourceLb i)
        _ = r := Nat.sub_add_cancel (hAllLe i)
    exact weighted_cover_infeasible_from_term_coverage
      (fun i => killSet D (sourceU i)) sourceLb lambda lambda0 target
      hLambda hTermCov hRowsAdd hrt hCert
  · push Not at hAllLe
    rcases hAllLe with ⟨i, hi⟩
    exact quotient_bound_exceeds_length (hWU i) D (hSource i) hi

end QiushiMatmul
