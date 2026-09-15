import QiushiPlane458GenData
import QiushiCertifiedTransport
import QiushiStep126Mono175From75
import QiushiStep99Orbit196Dispatch
import QiushiWcOrbit161Dispatch
import QiushiWcOrbit164Dispatch
import QiushiWcOrbit194Dispatch
import QiushiWcOrbit201Dispatch
import QiushiWcOrbit235Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane458GenSource0020 :
    QuotientRankAtLeast (spanCodes [321, 131, 35, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [340, 132, 32, 10, 1] [(321, 373), (131, 350), (35, 506), (20, 383), (10, 175)]
    (codeMat 407) (codeMat 375) (codeMat 491) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit201_lb16_wc

theorem plane458GenSource0021 :
    QuotientRankAtLeast (spanCodes [326, 132, 37, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [326, 136, 38, 20, 1] [(326, 373), (132, 326), (37, 488), (20, 327), (10, 509)]
    (codeMat 478) (codeMat 330) (codeMat 394) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit235_lb16_wc

theorem plane458GenSource0022 :
    QuotientRankAtLeast (spanCodes [324, 134, 39, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 96, 20, 10, 1] [(324, 126), (134, 287), (39, 21), (20, 31), (10, 20)]
    (codeMat 467) (codeMat 492) (codeMat 115) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit164_lb16_wc

theorem plane458GenSource0023 :
    QuotientRankAtLeast (spanCodes [323, 129, 35, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 160, 20, 10, 1] [(323, 170), (129, 191), (35, 434), (20, 180), (10, 274)]
    (codeMat 143) (codeMat 370) (codeMat 207) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit175_lb16_mono

theorem plane458GenSource0024 :
    QuotientRankAtLeast (spanCodes [352, 161, 20, 9, 3]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [340, 132, 32, 10, 1] [(352, 164), (161, 351), (20, 43), (9, 32), (3, 1)]
    (codeMat 409) (codeMat 482) (codeMat 143) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit201_lb16_wc

theorem plane458GenSource0025 :
    QuotientRankAtLeast (spanCodes [322, 128, 35, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [340, 132, 32, 10, 1] [(322, 11), (128, 1), (35, 341), (20, 133), (10, 506)]
    (codeMat 460) (codeMat 334) (codeMat 442) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit201_lb16_wc

theorem plane458GenSource0026 :
    QuotientRankAtLeast (spanCodes [323, 129, 34, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 132, 32, 10, 1] [(323, 269), (129, 175), (34, 10), (20, 11), (10, 42)]
    (codeMat 403) (codeMat 125) (codeMat 348) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit194_lb16_wc

theorem plane458GenSource0027 :
    QuotientRankAtLeast (spanCodes [326, 132, 39, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [288, 68, 20, 10, 1] [(326, 91), (132, 319), (39, 21), (20, 31), (10, 20)]
    (codeMat 275) (codeMat 492) (codeMat 115) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit161_lb16_wc

theorem plane458GenSource0028 :
    QuotientRankAtLeast (spanCodes [321, 131, 38, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 132, 32, 10, 1] [(321, 133), (131, 175), (38, 402), (20, 164), (10, 278)]
    (codeMat 143) (codeMat 339) (codeMat 467) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit196_lb16_unconditional

theorem plane458GenSource0029 :
    QuotientRankAtLeast (spanCodes [352, 162, 16, 10, 4]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [288, 68, 20, 10, 1] [(352, 20), (162, 68), (16, 1), (10, 78), (4, 288)]
    (codeMat 354) (codeMat 330) (codeMat 394) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit161_lb16_wc

end QiushiMatmul
