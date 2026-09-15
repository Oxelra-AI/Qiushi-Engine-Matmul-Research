import QiushiPlane491GenData
import QiushiCertifiedTransport
import QiushiOrbit35FP
import QiushiStep99Orbit65Dispatch
import QiushiStep99Orbit69Dispatch
import QiushiWcOrbit80Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane491GenSource0280 :
    QuotientRankAtLeast (spanCodes [258, 142, 74, 44, 30, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(258, 447), (142, 161), (74, 69), (44, 336), (30, 160), (1, 320)]
    (codeMat 94) (codeMat 359) (codeMat 174) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

theorem plane491GenSource0281 :
    QuotientRankAtLeast (spanCodes [265, 133, 73, 36, 29, 2]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(265, 26), (133, 69), (73, 27), (36, 16), (29, 496), (2, 320)]
    (codeMat 92) (codeMat 171) (codeMat 485) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

theorem plane491GenSource0282 :
    QuotientRankAtLeast (spanCodes [257, 136, 77, 40, 25, 3]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 164, 96, 16, 10, 1] [(257, 191), (136, 97), (77, 453), (40, 16), (25, 352), (3, 256)]
    (codeMat 87) (codeMat 359) (codeMat 174) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit69_lb15_unconditional

theorem plane491GenSource0283 :
    QuotientRankAtLeast (spanCodes [261, 137, 72, 41, 28, 3]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 164, 96, 16, 10, 1] [(261, 197), (137, 479), (72, 27), (41, 368), (28, 96), (3, 256)]
    (codeMat 93) (codeMat 415) (codeMat 253) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit69_lb15_unconditional

theorem plane491GenSource0284 :
    QuotientRankAtLeast (spanCodes [260, 128, 64, 33, 20, 2]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(260, 8), (128, 2), (64, 128), (33, 224), (20, 28), (2, 3)]
    (codeMat 165) (codeMat 98) (codeMat 140) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane491GenSource0285 :
    QuotientRankAtLeast (spanCodes [270, 132, 78, 38, 26, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(270, 286), (132, 447), (78, 261), (38, 496), (26, 336), (1, 320)]
    (codeMat 95) (codeMat 499) (codeMat 382) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

theorem plane491GenSource0286 :
    QuotientRankAtLeast (spanCodes [257, 137, 75, 42, 27, 4]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 96, 20, 10, 1] [(257, 357), (137, 368), (75, 272), (42, 223), (27, 192), (4, 260)]
    (codeMat 117) (codeMat 412) (codeMat 111) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit80_lb15_wc

theorem plane491GenSource0287 :
    QuotientRankAtLeast (spanCodes [256, 128, 67, 35, 17, 6]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(256, 8), (128, 9), (67, 139), (35, 227), (17, 252), (6, 3)]
    (codeMat 172) (codeMat 122) (codeMat 460) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane491GenSource0288 :
    QuotientRankAtLeast (spanCodes [264, 131, 72, 32, 26, 6]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(264, 26), (131, 447), (72, 1), (32, 16), (26, 496), (6, 320)]
    (codeMat 86) (codeMat 179) (codeMat 421) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

theorem plane491GenSource0289 :
    QuotientRankAtLeast (spanCodes [266, 137, 64, 42, 19, 7]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 96, 20, 10, 1] [(266, 181), (137, 283), (64, 192), (42, 180), (19, 420), (7, 432)]
    (codeMat 214) (codeMat 86) (codeMat 212) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit80_lb15_wc

end QiushiMatmul
