import QiushiPlane491GenData
import QiushiCertifiedTransport
import QiushiOrbit35FP
import QiushiStep128Mono189From80T
import QiushiStep99Orbit65Dispatch
import QiushiStep99Orbit69Dispatch
import QiushiWcOrbit220Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane491GenSource0310 :
    QuotientRankAtLeast (spanCodes [259, 146, 81, 49, 5]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [334, 192, 36, 16, 1] [(259, 37), (146, 192), (81, 228), (49, 398), (5, 16)]
    (codeMat 460) (codeMat 351) (codeMat 239) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit220_lb15_wc

theorem plane491GenSource0311 :
    QuotientRankAtLeast (spanCodes [258, 136, 74, 43, 27, 5]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 164, 96, 16, 10, 1] [(258, 368), (136, 447), (74, 463), (43, 26), (27, 1), (5, 16)]
    (codeMat 267) (codeMat 477) (codeMat 431) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit69_lb15_unconditional

theorem plane491GenSource0312 :
    QuotientRankAtLeast (spanCodes [267, 136, 67, 43, 19, 4]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(267, 234), (136, 28), (67, 255), (43, 232), (19, 224), (4, 128)]
    (codeMat 86) (codeMat 233) (codeMat 233) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane491GenSource0313 :
    QuotientRankAtLeast (spanCodes [261, 141, 72, 45, 28, 3]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(261, 430), (141, 177), (72, 27), (45, 320), (28, 160), (3, 16)]
    (codeMat 207) (codeMat 299) (codeMat 318) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

theorem plane491GenSource0314 :
    QuotientRankAtLeast (spanCodes [261, 141, 72, 44, 28, 2]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(261, 447), (141, 421), (72, 1), (44, 496), (28, 480), (2, 320)]
    (codeMat 86) (codeMat 423) (codeMat 181) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

theorem plane491GenSource0315 :
    QuotientRankAtLeast (spanCodes [272, 128, 80, 33, 4, 2]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(272, 20), (128, 2), (80, 148), (33, 104), (4, 8), (2, 1)]
    (codeMat 161) (codeMat 106) (codeMat 396) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane491GenSource0316 :
    QuotientRankAtLeast (spanCodes [262, 146, 84, 48, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 128, 32, 10, 1] [(262, 138), (146, 1), (84, 171), (48, 128), (1, 438)]
    (codeMat 167) (codeMat 110) (codeMat 444) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit189_lb15_mono

theorem plane491GenSource0317 :
    QuotientRankAtLeast (spanCodes [264, 136, 64, 42, 20, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(264, 150), (136, 149), (64, 2), (42, 96), (20, 232), (1, 128)]
    (codeMat 92) (codeMat 426) (codeMat 335) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane491GenSource0318 :
    QuotientRankAtLeast (spanCodes [261, 131, 65, 32, 21, 8]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(261, 22), (131, 148), (65, 2), (32, 9), (21, 104), (8, 1)]
    (codeMat 106) (codeMat 181) (codeMat 423) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane491GenSource0319 :
    QuotientRankAtLeast (spanCodes [263, 129, 64, 34, 20, 9]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(263, 232), (129, 104), (64, 8), (34, 150), (20, 148), (9, 1)]
    (codeMat 355) (codeMat 417) (codeMat 177) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

end QiushiMatmul
