import QiushiCodeSpanCore
import QiushiMonotonicity
import QiushiBranch262Extraction

set_option maxHeartbeats 4000000
open BigOperators Finset Matrix
namespace QiushiMatmul

/-- Orbit 412 (Wang dim-3, basis [12,2,1]) has quotient rank ≥ 17,
    by monotonicity from orbit 262 (basis [132,12,2,1], lb 17). -/
def o412W_mono : Submodule F2 Mat3 := spanCodes [12, 2, 1]

private theorem o412_containment :
    o412W_mono ≤ o262W := by
  unfold o412W_mono
  unfold spanCodes
  exact Submodule.span_le.mpr (by
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
    rcases hn with rfl | rfl | rfl
    · exact spanContainsCodeCore_implies_mem_spanCodes [132, 12, 2, 1] 12 (by decide)
    · exact spanContainsCodeCore_implies_mem_spanCodes [132, 12, 2, 1] 2 (by decide)
    · exact spanContainsCodeCore_implies_mem_spanCodes [132, 12, 2, 1] 1 (by decide))

theorem orbit412_lb17_mono : QuotientRankAtLeast o412W_mono 17 :=
  quotientRankAtLeast_mono o412_containment step113_orbit262_lb17

end QiushiMatmul
