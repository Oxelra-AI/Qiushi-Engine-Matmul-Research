import QiushiCodeSpanBridgeCore
import QiushiMonotonicity
import QiushiMonoOrbit417From279

set_option maxHeartbeats 4000000
open BigOperators Finset Matrix
namespace QiushiMatmul

/-- Orbit 479 (Wang dim-2, plane, basis [1,10]) has quotient rank ≥ 17,
    by literal containment in orbit 417 (basis [16,10,1], lb 17).

    span{1, 10} ⊆ span{16, 10, 1} because codes 1 and 10 are both
    literal generators of [16, 10, 1]. -/
def o479W_graded : Submodule F2 Mat3 := spanCodes [1, 10]

private theorem o479_containment_in_417 :
    o479W_graded ≤ o417W_mono := by
  unfold o479W_graded o417W_mono spanCodes
  exact Submodule.span_le.mpr (by
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
    rcases hn with rfl | rfl
    · exact spanContainsCodeCore_implies_mem_spanCodes [16, 10, 1] 1 (by decide)
    · exact spanContainsCodeCore_implies_mem_spanCodes [16, 10, 1] 10 (by decide))

/-- plane479 ≡ orbit 479 representative at lb ≥ 17. -/
theorem orbit479_lb17_graded : QuotientRankAtLeast o479W_graded 17 :=
  quotientRankAtLeast_mono o479_containment_in_417 orbit417_lb17_mono

end QiushiMatmul
