import QiushiCodeSpanCore
import QiushiMonotonicity
import QiushiMonoOrbit412From262

set_option maxHeartbeats 4000000
open BigOperators Finset Matrix
namespace QiushiMatmul

/-- Orbit 478 (Wang dim-2, basis [2,1]) has quotient rank ≥ 17,
    by monotonicity from orbit 412 (basis [12,2,1], lb 17). -/
def o478W_mono : Submodule F2 Mat3 := spanCodes [2, 1]

private theorem o478_containment :
    o478W_mono ≤ o412W_mono := by
  unfold o478W_mono
  unfold spanCodes
  exact Submodule.span_le.mpr (by
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
    rcases hn with rfl | rfl
    · exact spanContainsCodeCore_implies_mem_spanCodes [12, 2, 1] 2 (by decide)
    · exact spanContainsCodeCore_implies_mem_spanCodes [12, 2, 1] 1 (by decide))

theorem orbit478_lb17_mono : QuotientRankAtLeast o478W_mono 17 :=
  quotientRankAtLeast_mono o478_containment orbit412_lb17_mono

end QiushiMatmul
