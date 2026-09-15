import QiushiPlane426GenData
import QiushiCertifiedTransport
import QiushiOrbit29FP
import QiushiOrbit35FP
import QiushiStep99Orbit76Dispatch
import QiushiWcOrbit187Dispatch
import QiushiWcOrbit80Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane426GenSource0120 :
    QuotientRankAtLeast (spanCodes [272, 132, 70, 32, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 96, 20, 10, 1] [(272, 357), (132, 430), (70, 222), (32, 260), (10, 272), (1, 432)]
    (codeMat 158) (codeMat 348) (codeMat 125) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit80_lb15_wc

theorem plane426GenSource0121 :
    QuotientRankAtLeast (spanCodes [272, 150, 66, 54, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(272, 150), (150, 20), (66, 105), (54, 128), (10, 104), (1, 8)]
    (codeMat 206) (codeMat 417) (codeMat 177) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane426GenSource0122 :
    QuotientRankAtLeast (spanCodes [272, 148, 66, 50, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(272, 246), (148, 29), (66, 97), (50, 232), (10, 104), (1, 8)]
    (codeMat 143) (codeMat 419) (codeMat 183) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane426GenSource0123 :
    QuotientRankAtLeast (spanCodes [272, 162, 66, 10, 4, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(272, 224), (162, 104), (66, 151), (10, 148), (4, 128), (1, 2)]
    (codeMat 143) (codeMat 401) (codeMat 401) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane426GenSource0124 :
    QuotientRankAtLeast (spanCodes [272, 146, 112, 10, 6, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(272, 252), (146, 130), (112, 28), (10, 97), (6, 9), (1, 8)]
    (codeMat 185) (codeMat 426) (codeMat 335) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane426GenSource0125 :
    QuotientRankAtLeast (spanCodes [272, 162, 64, 10, 6, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(272, 232), (162, 245), (64, 128), (10, 149), (6, 3), (1, 2)]
    (codeMat 305) (codeMat 426) (codeMat 335) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane426GenSource0126 :
    QuotientRankAtLeast (spanCodes [272, 160, 66, 10, 6, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160] [(272, 68), (160, 69), (66, 170), (10, 168), (6, 8), (1, 16)]
    (codeMat 142) (codeMat 394) (codeMat 330) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit29_lb15

theorem plane426GenSource0127 :
    QuotientRankAtLeast (spanCodes [272, 208, 54, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 32, 10, 1] [(272, 429), (208, 301), (54, 390), (10, 268), (1, 32)]
    (codeMat 271) (codeMat 230) (codeMat 159) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit187_lb15_wc

theorem plane426GenSource0128 :
    QuotientRankAtLeast (spanCodes [272, 210, 52, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 32, 10, 1] [(272, 429), (210, 138), (52, 43), (10, 10), (1, 1)]
    (codeMat 409) (codeMat 307) (codeMat 311) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit187_lb15_wc

theorem plane426GenSource0129 :
    QuotientRankAtLeast (spanCodes [272, 132, 80, 50, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [288, 160, 68, 20, 10, 1] [(272, 367), (132, 453), (80, 366), (50, 464), (10, 240), (1, 384)]
    (codeMat 92) (codeMat 494) (codeMat 501) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit76_lb15_unconditional

end QiushiMatmul
