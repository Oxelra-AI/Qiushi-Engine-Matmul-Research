import QiushiPlane476GenData
import QiushiCertifiedTransport
import QiushiOrbit35FP
import QiushiStep99Orbit65Dispatch
import QiushiWcOrbit80Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane476GenSource0050 :
    QuotientRankAtLeast (spanCodes [276, 128, 65, 33, 8, 2]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(276, 20), (128, 130), (65, 1), (33, 96), (8, 8), (2, 128)]
    (codeMat 85) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane476GenSource0051 :
    QuotientRankAtLeast (spanCodes [274, 129, 64, 32, 10, 6]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 96, 20, 10, 1] [(274, 202), (129, 283), (64, 192), (32, 432), (10, 420), (6, 260)]
    (codeMat 95) (codeMat 370) (codeMat 207) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit80_lb15_wc

theorem plane476GenSource0052 :
    QuotientRankAtLeast (spanCodes [274, 147, 82, 50, 10, 6]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 96, 20, 10, 1] [(274, 20), (147, 378), (82, 21), (50, 272), (10, 464), (6, 432)]
    (codeMat 156) (codeMat 337) (codeMat 337) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit80_lb15_wc

theorem plane476GenSource0053 :
    QuotientRankAtLeast (spanCodes [260, 133, 69, 37, 16, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 96, 20, 10, 1] [(260, 1), (133, 202), (69, 10), (37, 20), (16, 432), (10, 160)]
    (codeMat 205) (codeMat 156) (codeMat 102) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit80_lb15_wc

theorem plane476GenSource0054 :
    QuotientRankAtLeast (spanCodes [256, 132, 64, 32, 20, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(256, 2), (132, 20), (64, 128), (32, 3), (20, 28), (10, 224)]
    (codeMat 102) (codeMat 84) (codeMat 84) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane476GenSource0055 :
    QuotientRankAtLeast (spanCodes [256, 128, 68, 36, 20, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(256, 2), (128, 3), (68, 150), (36, 128), (20, 136), (10, 232)]
    (codeMat 212) (codeMat 122) (codeMat 460) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane476GenSource0056 :
    QuotientRankAtLeast (spanCodes [260, 130, 67, 35, 16, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(260, 128), (130, 2), (67, 22), (35, 224), (16, 3), (10, 31)]
    (codeMat 111) (codeMat 267) (codeMat 282) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane476GenSource0057 :
    QuotientRankAtLeast (spanCodes [262, 130, 65, 33, 18, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(262, 150), (130, 2), (65, 3), (33, 232), (18, 128), (10, 136)]
    (codeMat 213) (codeMat 313) (codeMat 313) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane476GenSource0058 :
    QuotientRankAtLeast (spanCodes [260, 135, 69, 37, 16, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(260, 1), (135, 506), (69, 78), (37, 496), (16, 16), (10, 160)]
    (codeMat 213) (codeMat 92) (codeMat 116) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

theorem plane476GenSource0059 :
    QuotientRankAtLeast (spanCodes [256, 133, 66, 34, 20, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(256, 260), (133, 238), (66, 497), (34, 176), (20, 160), (10, 496)]
    (codeMat 158) (codeMat 401) (codeMat 401) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

end QiushiMatmul
