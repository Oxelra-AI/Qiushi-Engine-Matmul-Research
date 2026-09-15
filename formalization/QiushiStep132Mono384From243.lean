import QiushiCodeSpanBridgeCore
import QiushiMonotonicity
import QiushiStep126Mono243From85

set_option maxHeartbeats 4000000
open BigOperators Finset Matrix
namespace QiushiMatmul

def o384W_mono : Submodule F2 Mat3 := spanCodes [68, 35, 20, 10]

private theorem o384_containment :
    o384W_mono ≤ o243W_mono := by
  unfold o384W_mono o243W_mono spanCodes
  exact Submodule.span_le.mpr (by
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hn
    rcases hn with rfl | rfl | rfl | rfl
    · exact spanContainsCodeCore_implies_mem_spanCodes [131, 68, 35, 20, 10] 68 (by decide)
    · exact spanContainsCodeCore_implies_mem_spanCodes [131, 68, 35, 20, 10] 35 (by decide)
    · exact spanContainsCodeCore_implies_mem_spanCodes [131, 68, 35, 20, 10] 20 (by decide)
    · exact spanContainsCodeCore_implies_mem_spanCodes [131, 68, 35, 20, 10] 10 (by decide))

theorem orbit384_lb17_mono : QuotientRankAtLeast o384W_mono 17 :=
  quotientRankAtLeast_mono o384_containment orbit243_lb17_mono

end QiushiMatmul
