import QiushiPlane461GenData
import QiushiCertifiedTransport
import QiushiOrbit35FP
import QiushiStep99Orbit65Dispatch
import QiushiStep99Orbit69Dispatch
import QiushiWcOrbit72Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane461GenSource0050 :
    QuotientRankAtLeast (spanCodes [276, 134, 68, 36, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(276, 245), (134, 430), (68, 186), (36, 320), (10, 160), (1, 16)]
    (codeMat 206) (codeMat 412) (codeMat 111) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

theorem plane461GenSource0051 :
    QuotientRankAtLeast (spanCodes [288, 162, 68, 16, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(288, 260), (162, 228), (68, 176), (16, 27), (10, 10), (1, 16)]
    (codeMat 331) (codeMat 282) (codeMat 267) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

theorem plane461GenSource0052 :
    QuotientRankAtLeast (spanCodes [256, 128, 68, 34, 16, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(256, 8), (128, 1), (68, 104), (34, 20), (16, 2), (10, 148)]
    (codeMat 84) (codeMat 106) (codeMat 396) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane461GenSource0053 :
    QuotientRankAtLeast (spanCodes [258, 130, 68, 32, 16, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(258, 136), (130, 128), (68, 232), (32, 3), (16, 2), (10, 150)]
    (codeMat 354) (codeMat 124) (codeMat 124) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane461GenSource0054 :
    QuotientRankAtLeast (spanCodes [257, 128, 68, 34, 16, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(257, 104), (128, 128), (68, 96), (34, 148), (16, 2), (10, 149)]
    (codeMat 298) (codeMat 337) (codeMat 337) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane461GenSource0055 :
    QuotientRankAtLeast (spanCodes [259, 130, 68, 32, 16, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(259, 224), (130, 3), (68, 255), (32, 128), (16, 2), (10, 150)]
    (codeMat 87) (codeMat 331) (codeMat 410) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane461GenSource0056 :
    QuotientRankAtLeast (spanCodes [261, 132, 68, 38, 16, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 164, 96, 16, 10, 1] [(261, 222), (132, 436), (68, 437), (38, 272), (16, 256), (10, 96)]
    (codeMat 156) (codeMat 481) (codeMat 185) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit69_lb15_unconditional

theorem plane461GenSource0057 :
    QuotientRankAtLeast (spanCodes [260, 148, 68, 54, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(260, 27), (148, 430), (68, 26), (54, 320), (10, 160), (1, 16)]
    (codeMat 204) (codeMat 188) (codeMat 103) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

theorem plane461GenSource0058 :
    QuotientRankAtLeast (spanCodes [276, 132, 68, 38, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(276, 79), (132, 446), (68, 186), (38, 496), (10, 160), (1, 16)]
    (codeMat 207) (codeMat 444) (codeMat 110) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

theorem plane461GenSource0059 :
    QuotientRankAtLeast (spanCodes [258, 128, 68, 34, 20, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 68, 32, 20, 10, 1] [(258, 264), (128, 32), (68, 112), (34, 265), (20, 100), (10, 310)]
    (codeMat 102) (codeMat 204) (codeMat 114) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit72_lb15_wc

end QiushiMatmul
