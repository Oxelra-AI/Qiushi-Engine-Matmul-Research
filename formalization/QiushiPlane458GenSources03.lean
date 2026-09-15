import QiushiPlane458GenData
import QiushiCertifiedTransport
import QiushiStep99Orbit196Dispatch
import QiushiWcOrbit161Dispatch
import QiushiWcOrbit164Dispatch
import QiushiWcOrbit194Dispatch
import QiushiWcOrbit201Dispatch
import QiushiWcOrbit235Dispatch
import QiushiWcOrbit238Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane458GenSource0030 :
    QuotientRankAtLeast (spanCodes [320, 130, 37, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [340, 132, 32, 10, 1] [(320, 1), (130, 32), (37, 506), (20, 341), (10, 464)]
    (codeMat 348) (codeMat 380) (codeMat 117) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit201_lb16_wc

theorem plane458GenSource0031 :
    QuotientRankAtLeast (spanCodes [327, 133, 34, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 132, 32, 10, 1] [(327, 310), (133, 164), (34, 10), (20, 11), (10, 42)]
    (codeMat 275) (codeMat 125) (codeMat 348) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit196_lb16_unconditional

theorem plane458GenSource0032 :
    QuotientRankAtLeast (spanCodes [324, 134, 33, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 132, 32, 10, 1] [(324, 175), (134, 133), (33, 278), (20, 132), (10, 434)]
    (codeMat 207) (codeMat 334) (codeMat 442) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit196_lb16_unconditional

theorem plane458GenSource0033 :
    QuotientRankAtLeast (spanCodes [258, 167, 103, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [294, 136, 96, 20, 1] [(258, 326), (167, 117), (103, 116), (20, 232), (10, 96)]
    (codeMat 92) (codeMat 482) (codeMat 143) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit238_lb16_wc

theorem plane458GenSource0034 :
    QuotientRankAtLeast (spanCodes [259, 132, 69, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [326, 136, 38, 20, 1] [(259, 488), (132, 327), (69, 338), (20, 326), (10, 51)]
    (codeMat 494) (codeMat 267) (codeMat 282) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit235_lb16_wc

theorem plane458GenSource0035 :
    QuotientRankAtLeast (spanCodes [256, 162, 96, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 96, 20, 10, 1] [(256, 1), (162, 352), (96, 11), (20, 97), (10, 373)]
    (codeMat 468) (codeMat 143) (codeMat 482) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit164_lb16_wc

theorem plane458GenSource0036 :
    QuotientRankAtLeast (spanCodes [257, 132, 71, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [288, 68, 20, 10, 1] [(257, 21), (132, 31), (71, 30), (20, 319), (10, 356)]
    (codeMat 165) (codeMat 485) (codeMat 171) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit161_lb16_wc

theorem plane458GenSource0037 :
    QuotientRankAtLeast (spanCodes [257, 134, 69, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 132, 32, 10, 1] [(257, 164), (134, 434), (69, 402), (20, 435), (10, 43)]
    (codeMat 359) (codeMat 303) (codeMat 286) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit196_lb16_unconditional

theorem plane458GenSource0038 :
    QuotientRankAtLeast (spanCodes [257, 163, 96, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 96, 20, 10, 1] [(257, 363), (163, 372), (96, 373), (20, 287), (10, 126)]
    (codeMat 501) (codeMat 254) (codeMat 443) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit164_lb16_wc

theorem plane458GenSource0039 :
    QuotientRankAtLeast (spanCodes [262, 132, 64, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 132, 32, 10, 1] [(262, 132), (132, 386), (64, 1), (20, 418), (10, 269)]
    (codeMat 372) (codeMat 417) (codeMat 177) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit194_lb16_wc

end QiushiMatmul
