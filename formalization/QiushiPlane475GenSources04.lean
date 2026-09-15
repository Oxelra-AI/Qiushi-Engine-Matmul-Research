import QiushiPlane475GenData
import QiushiCertifiedTransport
import QiushiOrbit29FP
import QiushiOrbit35FP
import QiushiStep99Orbit217Dispatch
import QiushiWcOrbit214Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane475GenSource0040 :
    QuotientRankAtLeast (spanCodes [256, 147, 86, 54, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 132, 96, 10, 1] [(256, 1), (147, 374), (86, 499), (54, 504), (10, 408)]
    (codeMat 84) (codeMat 157) (codeMat 486) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit214_lb16_wc

theorem plane475GenSource0041 :
    QuotientRankAtLeast (spanCodes [276, 135, 66, 34, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 132, 96, 10, 1] [(276, 238), (135, 381), (66, 97), (34, 408), (10, 96)]
    (codeMat 206) (codeMat 419) (codeMat 183) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit214_lb16_wc

theorem plane475GenSource0042 :
    QuotientRankAtLeast (spanCodes [292, 165, 96, 19, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [308, 132, 96, 10, 1] [(292, 1), (165, 309), (96, 96), (19, 319), (10, 475)]
    (codeMat 167) (codeMat 86) (codeMat 212) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit217_lb16_unconditional

theorem plane475GenSource0043 :
    QuotientRankAtLeast (spanCodes [307, 161, 96, 10, 4]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 132, 96, 10, 1] [(307, 375), (161, 107), (96, 133), (10, 408), (4, 504)]
    (codeMat 158) (codeMat 375) (codeMat 491) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit214_lb16_wc

theorem plane475GenSource0044 :
    QuotientRankAtLeast (spanCodes [164, 96, 16, 8, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160] [(164, 228), (96, 68), (16, 3), (8, 1), (2, 24), (1, 8)]
    (codeMat 266) (codeMat 275) (codeMat 275) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit29_lb15

theorem plane475GenSource0045 :
    QuotientRankAtLeast (spanCodes [161, 96, 17, 9, 4, 3]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(161, 244), (96, 224), (17, 11), (9, 8), (4, 128), (3, 2)]
    (codeMat 267) (codeMat 282) (codeMat 267) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane475GenSource0046 :
    QuotientRankAtLeast (spanCodes [164, 96, 20, 8, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(164, 252), (96, 104), (20, 28), (8, 8), (2, 3), (1, 1)]
    (codeMat 401) (codeMat 275) (codeMat 275) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane475GenSource0047 :
    QuotientRankAtLeast (spanCodes [132, 65, 33, 16, 8, 2]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(132, 104), (65, 128), (33, 20), (16, 1), (8, 2), (2, 8)]
    (codeMat 330) (codeMat 266) (codeMat 266) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane475GenSource0048 :
    QuotientRankAtLeast (spanCodes [148, 80, 48, 8, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(148, 126), (80, 22), (48, 130), (8, 2), (2, 9), (1, 1)]
    (codeMat 273) (codeMat 307) (codeMat 311) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane475GenSource0049 :
    QuotientRankAtLeast (spanCodes [129, 68, 36, 16, 8, 2]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(129, 28), (68, 224), (36, 128), (16, 1), (8, 8), (2, 3)]
    (codeMat 282) (codeMat 266) (codeMat 266) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

end QiushiMatmul
