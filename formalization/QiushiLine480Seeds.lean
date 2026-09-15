import QiushiCertifiedTransport
import QiushiStep104Orbit279Split

namespace QiushiMatmul

-- Recheck the two existing seed transports without requiring their flat caches.
theorem line480_seed424_lb17 :
    QuotientRankAtLeast (spanCodes [256, 10, 1]) 17 := by
  exact quotientRankAtLeast_of_code_transport
    [68, 16, 10, 1] [(256, 16), (10, 68), (1, 1)]
    (codeMat 161) (codeMat 161) (codeMat 161) false
    (by decide) (by decide) (by decide) (by decide)
    step104_orbit279_lb17

theorem line480_seed431_lb17 :
    QuotientRankAtLeast (spanCodes [228, 16, 1]) 17 := by
  exact quotientRankAtLeast_of_code_transport
    [68, 16, 10, 1] [(228, 68), (16, 27), (1, 16)]
    (codeMat 267) (codeMat 282) (codeMat 267) false
    (by decide) (by decide) (by decide) (by decide)
    step104_orbit279_lb17

#print axioms line480_seed424_lb17
#print axioms line480_seed431_lb17

end QiushiMatmul
