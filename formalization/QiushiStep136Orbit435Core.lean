import QiushiStep136Orbit435CovDispatch
import QiushiStep136Orbit435CoverSound
import QiushiStep136Orbit435Wle
import QiushiStep131Orbit451CoreBoolV3

set_option maxHeartbeats 800000000
set_option maxRecDepth 10000
set_option linter.unusedVariables false
open BigOperators Finset Matrix Classical
attribute [local instance] Classical.propDecidable
noncomputable section
namespace QiushiMatmul

private theorem o435CertDirect : (125635560 - 12158280) * 16 < ∑ i : Fin 63, o435Lambda i * o435SourceLb i := by
  simp only [o435Lambda, o435SourceLb]
  decide

private theorem o435LambdaSumDirect : 12158280 ≤ ∑ i : Fin 63, o435Lambda i := by
  simp only [o435Lambda]
  decide

theorem o435ScalarLb17
    (hSource : ∀ i : Fin 63, QuotientRankAtLeast (o435SourceU i) (o435SourceLb i)) :
    QuotientRankAtLeast o435W 17 :=
  quotientRankAtLeast_of_contradiction o435W 17 (fun r hr D =>
    direct_coverage_quotient_decomp_false_of_boolEq_cover
      o435SourceU o435SourceLb o435Lambda
      12158280 16
      (fun i M => o435ScalarCoverB i
        (evalFunc (o435AnnBasis ⟨0, by decide⟩) M)
        (evalFunc (o435AnnBasis ⟨1, by decide⟩) M)
        (evalFunc (o435AnnBasis ⟨2, by decide⟩) M)
        (evalFunc (o435AnnBasis ⟨3, by decide⟩) M)
        (evalFunc (o435AnnBasis ⟨4, by decide⟩) M)
        (evalFunc (o435AnnBasis ⟨5, by decide⟩) M)
      )
      o435W_le_source hSource
      o435LambdaSumDirect
      (by
        intro i M h
        exact o435CoverSound i M h)
      (fun M => o435ScalarCoverage
        (evalFunc (o435AnnBasis ⟨0, by decide⟩) M)
        (evalFunc (o435AnnBasis ⟨1, by decide⟩) M)
        (evalFunc (o435AnnBasis ⟨2, by decide⟩) M)
        (evalFunc (o435AnnBasis ⟨3, by decide⟩) M)
        (evalFunc (o435AnnBasis ⟨4, by decide⟩) M)
        (evalFunc (o435AnnBasis ⟨5, by decide⟩) M)
      )
      (by omega) o435CertDirect D)

end QiushiMatmul
end
