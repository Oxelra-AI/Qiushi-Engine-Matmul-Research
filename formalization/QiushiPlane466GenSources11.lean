import QiushiPlane466GenData
import QiushiCertifiedTransport
import QiushiOrbit35FP
import QiushiStep128Mono189From80T
import QiushiStep99Orbit65Dispatch
import QiushiStep99Orbit69Dispatch
import QiushiWcOrbit80Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane466GenSource0110 :
    QuotientRankAtLeast (spanCodes [256, 133, 68, 35, 18, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 96, 20, 10, 1] [(256, 260), (133, 203), (68, 357), (35, 272), (18, 192), (10, 368)]
    (codeMat 207) (codeMat 339) (codeMat 467) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit80_lb15_wc

theorem plane466GenSource0111 :
    QuotientRankAtLeast (spanCodes [256, 132, 68, 32, 17, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(256, 2), (132, 148), (68, 149), (32, 128), (17, 104), (10, 96)]
    (codeMat 156) (codeMat 225) (codeMat 169) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane466GenSource0112 :
    QuotientRankAtLeast (spanCodes [290, 166, 68, 18, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(290, 446), (166, 78), (68, 176), (18, 1), (10, 26), (1, 16)]
    (codeMat 267) (codeMat 298) (codeMat 270) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

theorem plane466GenSource0113 :
    QuotientRankAtLeast (spanCodes [304, 176, 64, 10, 4, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(304, 96), (176, 104), (64, 1), (10, 148), (4, 128), (1, 2)]
    (codeMat 140) (codeMat 401) (codeMat 401) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane466GenSource0114 :
    QuotientRankAtLeast (spanCodes [304, 178, 66, 10, 6, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(304, 232), (178, 245), (66, 21), (10, 149), (6, 3), (1, 2)]
    (codeMat 417) (codeMat 426) (codeMat 335) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane466GenSource0115 :
    QuotientRankAtLeast (spanCodes [256, 135, 68, 49, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 128, 32, 10, 1] [(256, 32), (135, 170), (68, 284), (49, 139), (10, 413)]
    (codeMat 423) (codeMat 395) (codeMat 474) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit189_lb15_mono

theorem plane466GenSource0116 :
    QuotientRankAtLeast (spanCodes [256, 135, 68, 37, 20, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 96, 20, 10, 1] [(256, 260), (135, 356), (68, 357), (37, 170), (20, 378), (10, 21)]
    (codeMat 285) (codeMat 286) (codeMat 303) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit80_lb15_wc

theorem plane466GenSource0117 :
    QuotientRankAtLeast (spanCodes [262, 129, 68, 37, 18, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 96, 20, 10, 1] [(262, 367), (129, 378), (68, 191), (37, 420), (18, 432), (10, 180)]
    (codeMat 142) (codeMat 445) (codeMat 478) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit80_lb15_wc

theorem plane466GenSource0118 :
    QuotientRankAtLeast (spanCodes [260, 131, 68, 37, 16, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 96, 20, 10, 1] [(260, 432), (131, 430), (68, 368), (37, 96), (16, 260), (10, 357)]
    (codeMat 187) (codeMat 426) (codeMat 335) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit80_lb15_wc

theorem plane466GenSource0119 :
    QuotientRankAtLeast (spanCodes [261, 131, 68, 38, 18, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 164, 96, 16, 10, 1] [(261, 437), (131, 436), (68, 222), (38, 96), (18, 256), (10, 272)]
    (codeMat 213) (codeMat 460) (codeMat 122) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit69_lb15_unconditional

end QiushiMatmul
