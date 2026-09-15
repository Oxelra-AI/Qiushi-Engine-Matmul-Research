import QiushiStep130Orbit451FixedDispatch
import QiushiStep130Orbit451CoverSoundV2
import QiushiStep129Orbit451FastWleV2
import QiushiDirectCoverage

set_option maxHeartbeats 400000000
set_option maxRecDepth 10000
set_option linter.unusedVariables false
open BigOperators Finset Matrix Classical
attribute [local instance] Classical.propDecidable
noncomputable section
namespace QiushiMatmul

/-- Direct-coverage contradiction using a Boolean cover predicate, with the
matrix coverage inequality stated in the exact `if cover i M = true` form
provided by the scalar-state dispatcher.  This avoids the expensive conversion
from the Prop predicate `o451Cover` to its Boolean equality definition. -/
theorem direct_coverage_quotient_decomp_false_of_boolEq_cover
    {m r : ℕ}
    {W : Submodule F2 Mat3}
    (sourceU : Fin m → Submodule F2 Mat3)
    (sourceLb : Fin m → ℕ)
    (lambda : Fin m → ℕ) (lambda0 target : ℕ)
    (cover : Fin m → Mat3 → Bool)
    (hWU : ∀ i : Fin m, W ≤ sourceU i)
    (hSource : ∀ i : Fin m, QuotientRankAtLeast (sourceU i) (sourceLb i))
    (hLambda : lambda0 ≤ ∑ i : Fin m, lambda i)
    (hCoverSound : ∀ (i : Fin m) (M : Mat3), cover i M = true → M ∈ sourceU i)
    (hMatCov : ∀ M : Mat3, lambda0 ≤ ∑ i : Fin m,
      if cover i M = true then lambda i else 0)
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
      by_cases hc : cover i (D.A t) = true
      · have ht : t ∈ killSet D (sourceU i) := by
          simp only [killSet, Finset.mem_filter, Finset.mem_univ, true_and]
          exact hCoverSound i (D.A t) hc
        simp [hc, ht]
      · have hf : cover i (D.A t) = false := by
          cases hb : cover i (D.A t) <;> simp_all
        simp [hf]
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

private theorem o451Cert : (360 - 40) * 17 < ∑ i : Fin 44, o451Lambda i * o451SourceLb i := by
  simp only [o451Lambda, o451SourceLb]
  decide

private theorem o451LambdaSum : 40 ≤ ∑ i : Fin 44, o451Lambda i := by
  simp only [o451Lambda]
  decide

/-- Conditional weighted-cover lower bound for orbit451, using the Boolean
coverage interface to avoid matrix-level cover conversion. -/
theorem o451ScalarLb18
    (hSource : ∀ i : Fin 44, QuotientRankAtLeast (o451SourceU i) (o451SourceLb i)) :
    QuotientRankAtLeast o451W 18 :=
  quotientRankAtLeast_of_contradiction o451W 18 (fun r hr D =>
    direct_coverage_quotient_decomp_false_of_boolEq_cover
      o451SourceU o451SourceLb o451Lambda
      40 17
      (fun i M => o451ScalarCoverB i
        (evalFunc (o451AnnBasis ⟨0, by decide⟩) M) (evalFunc (o451AnnBasis ⟨1, by decide⟩) M)
        (evalFunc (o451AnnBasis ⟨2, by decide⟩) M) (evalFunc (o451AnnBasis ⟨3, by decide⟩) M)
        (evalFunc (o451AnnBasis ⟨4, by decide⟩) M) (evalFunc (o451AnnBasis ⟨5, by decide⟩) M))
      o451W_le_source hSource
      o451LambdaSum
      (by
        intro i M h
        exact o451CoverSound i M h)
      (fun M => o451ScalarCoverage
        (evalFunc (o451AnnBasis ⟨0, by decide⟩) M) (evalFunc (o451AnnBasis ⟨1, by decide⟩) M)
        (evalFunc (o451AnnBasis ⟨2, by decide⟩) M) (evalFunc (o451AnnBasis ⟨3, by decide⟩) M)
        (evalFunc (o451AnnBasis ⟨4, by decide⟩) M) (evalFunc (o451AnnBasis ⟨5, by decide⟩) M))
      (by omega) o451Cert D)

end QiushiMatmul
end
