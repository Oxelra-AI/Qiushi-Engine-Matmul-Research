import QiushiPlane469GenData
import QiushiCertifiedTransport
import QiushiStep99Orbit196Dispatch
import QiushiWcOrbit201Dispatch
import QiushiWcOrbit204Dispatch
import QiushiWcOrbit214Dispatch
import QiushiWcOrbit238Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane469GenSource0010 :
    QuotientRankAtLeast (spanCodes [258, 135, 65, 21, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 132, 32, 10, 1] [(258, 434), (135, 132), (65, 32), (21, 133), (10, 42)]
    (codeMat 335) (codeMat 298) (codeMat 270) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit196_lb16_unconditional

theorem plane469GenSource0011 :
    QuotientRankAtLeast (spanCodes [258, 135, 71, 19, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 132, 32, 10, 1] [(258, 42), (135, 11), (71, 43), (19, 164), (10, 402)]
    (codeMat 165) (codeMat 380) (codeMat 117) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit196_lb16_unconditional

theorem plane469GenSource0012 :
    QuotientRankAtLeast (spanCodes [258, 147, 83, 10, 7]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 132, 32, 10, 1] [(258, 42), (147, 132), (83, 164), (10, 434), (7, 1)]
    (codeMat 417) (codeMat 348) (codeMat 125) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit196_lb16_unconditional

theorem plane469GenSource0013 :
    QuotientRankAtLeast (spanCodes [258, 133, 68, 16, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [340, 132, 32, 10, 1] [(258, 506), (133, 133), (68, 175), (16, 1), (10, 11)]
    (codeMat 458) (codeMat 299) (codeMat 318) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit201_lb16_wc

theorem plane469GenSource0014 :
    QuotientRankAtLeast (spanCodes [258, 145, 80, 10, 4]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [340, 132, 32, 10, 1] [(258, 11), (145, 133), (80, 175), (10, 506), (4, 1)]
    (codeMat 489) (codeMat 93) (codeMat 372) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit201_lb16_wc

theorem plane469GenSource0015 :
    QuotientRankAtLeast (spanCodes [258, 147, 82, 10, 6]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [340, 132, 32, 10, 1] [(258, 33), (147, 341), (82, 383), (10, 464), (6, 32)]
    (codeMat 205) (codeMat 207) (codeMat 370) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit201_lb16_wc

theorem plane469GenSource0016 :
    QuotientRankAtLeast (spanCodes [258, 132, 84, 37, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [274, 176, 68, 10, 1] [(258, 69), (132, 68), (84, 419), (37, 424), (10, 280)]
    (codeMat 85) (codeMat 397) (codeMat 250) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit204_lb16_wc

theorem plane469GenSource0017 :
    QuotientRankAtLeast (spanCodes [258, 149, 84, 52, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [274, 176, 68, 10, 1] [(258, 274), (149, 68), (84, 187), (52, 176), (10, 280)]
    (codeMat 86) (codeMat 169) (codeMat 225) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit204_lb16_wc

theorem plane469GenSource0018 :
    QuotientRankAtLeast (spanCodes [258, 151, 84, 51, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 132, 96, 10, 1] [(258, 408), (151, 11), (84, 499), (51, 381), (10, 284)]
    (codeMat 270) (codeMat 370) (codeMat 207) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit214_lb16_wc

theorem plane469GenSource0019 :
    QuotientRankAtLeast (spanCodes [258, 129, 84, 36, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [294, 136, 96, 20, 1] [(258, 326), (129, 430), (84, 474), (36, 1), (10, 97)]
    (codeMat 187) (codeMat 207) (codeMat 370) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit238_lb16_wc

end QiushiMatmul
