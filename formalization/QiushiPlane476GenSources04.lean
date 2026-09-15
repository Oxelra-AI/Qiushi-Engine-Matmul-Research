import QiushiPlane476GenData
import QiushiCertifiedTransport
import QiushiOrbit35FP
import QiushiStep99Orbit65Dispatch
import QiushiWcOrbit214Dispatch
import QiushiWcOrbit80Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane476GenSource0040 :
    QuotientRankAtLeast (spanCodes [272, 179, 96, 10, 4]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 132, 96, 10, 1] [(272, 408), (179, 143), (96, 238), (10, 381), (4, 504)]
    (codeMat 477) (codeMat 369) (codeMat 377) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit214_lb16_wc

theorem plane476GenSource0041 :
    QuotientRankAtLeast (spanCodes [276, 181, 96, 8, 2]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 132, 96, 10, 1] [(276, 96), (181, 239), (96, 10), (8, 1), (2, 504)]
    (codeMat 482) (codeMat 177) (codeMat 417) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit214_lb16_wc

theorem plane476GenSource0042 :
    QuotientRankAtLeast (spanCodes [272, 64, 32, 10, 4, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(272, 96), (64, 128), (32, 8), (10, 20), (4, 1), (1, 2)]
    (codeMat 273) (codeMat 140) (codeMat 98) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane476GenSource0043 :
    QuotientRankAtLeast (spanCodes [272, 66, 34, 10, 4, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(272, 232), (66, 150), (34, 30), (10, 22), (4, 3), (1, 2)]
    (codeMat 401) (codeMat 188) (codeMat 103) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane476GenSource0044 :
    QuotientRankAtLeast (spanCodes [276, 68, 36, 8, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(276, 246), (68, 22), (36, 9), (8, 3), (2, 128), (1, 2)]
    (codeMat 267) (codeMat 165) (codeMat 163) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane476GenSource0045 :
    QuotientRankAtLeast (spanCodes [256, 128, 96, 16, 10, 4]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(256, 2), (128, 1), (96, 20), (16, 8), (10, 96), (4, 128)]
    (codeMat 84) (codeMat 98) (codeMat 140) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane476GenSource0046 :
    QuotientRankAtLeast (spanCodes [257, 129, 96, 21, 8, 2]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 96, 20, 10, 1] [(257, 463), (129, 462), (96, 357), (21, 272), (8, 260), (2, 432)]
    (codeMat 156) (codeMat 501) (codeMat 494) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit80_lb15_wc

theorem plane476GenSource0047 :
    QuotientRankAtLeast (spanCodes [256, 129, 96, 20, 8, 2]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(256, 260), (129, 170), (96, 69), (20, 160), (8, 320), (2, 16)]
    (codeMat 142) (codeMat 337) (codeMat 337) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

theorem plane476GenSource0048 :
    QuotientRankAtLeast (spanCodes [261, 132, 96, 17, 8, 2]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(261, 436), (132, 78), (96, 160), (17, 10), (8, 16), (2, 1)]
    (codeMat 401) (codeMat 298) (codeMat 270) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

theorem plane476GenSource0049 :
    QuotientRankAtLeast (spanCodes [260, 134, 96, 16, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(260, 16), (134, 160), (96, 490), (16, 260), (10, 69), (1, 320)]
    (codeMat 107) (codeMat 225) (codeMat 169) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

end QiushiMatmul
