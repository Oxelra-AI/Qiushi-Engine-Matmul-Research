import QiushiPlane491GenData
import QiushiCertifiedTransport
import QiushiMonoOrbit149From65
import QiushiOrbit35FP
import QiushiStep128Mono189From80T
import QiushiStep99Orbit65Dispatch
import QiushiStep99Orbit69Dispatch
import QiushiWcOrbit80Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane491GenSource0260 :
    QuotientRankAtLeast (spanCodes [256, 128, 80, 34, 4, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(256, 1), (128, 8), (80, 96), (34, 20), (4, 2), (1, 128)]
    (codeMat 140) (codeMat 84) (codeMat 84) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane491GenSource0261 :
    QuotientRankAtLeast (spanCodes [273, 146, 84, 49, 9]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 68, 16, 10, 1] [(273, 267), (146, 325), (84, 266), (49, 272), (9, 16)]
    (codeMat 157) (codeMat 174) (codeMat 359) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit149_lb15_mono

theorem plane491GenSource0262 :
    QuotientRankAtLeast (spanCodes [276, 147, 84, 48, 15]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 128, 32, 10, 1] [(276, 439), (147, 413), (84, 311), (48, 1), (15, 33)]
    (codeMat 226) (codeMat 445) (codeMat 478) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit189_lb15_mono

theorem plane491GenSource0263 :
    QuotientRankAtLeast (spanCodes [276, 145, 84, 49, 13, 3]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(276, 287), (145, 347), (84, 286), (49, 160), (13, 496), (3, 320)]
    (codeMat 92) (codeMat 382) (codeMat 499) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

theorem plane491GenSource0264 :
    QuotientRankAtLeast (spanCodes [274, 150, 84, 52, 12, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 96, 20, 10, 1] [(274, 191), (150, 283), (84, 431), (52, 356), (12, 357), (1, 260)]
    (codeMat 98) (codeMat 375) (codeMat 491) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit80_lb15_wc

theorem plane491GenSource0265 :
    QuotientRankAtLeast (spanCodes [275, 146, 80, 49, 10, 4]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 164, 96, 16, 10, 1] [(275, 122), (146, 27), (80, 437), (49, 96), (10, 368), (4, 16)]
    (codeMat 206) (codeMat 115) (codeMat 492) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit69_lb15_unconditional

theorem plane491GenSource0266 :
    QuotientRankAtLeast (spanCodes [272, 145, 80, 50, 10, 4]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 96, 20, 10, 1] [(272, 223), (145, 191), (80, 367), (50, 452), (10, 453), (4, 192)]
    (codeMat 106) (codeMat 247) (codeMat 379) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit80_lb15_wc

theorem plane491GenSource0267 :
    QuotientRankAtLeast (spanCodes [257, 131, 81, 32, 8, 5]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(257, 136), (131, 224), (81, 28), (32, 1), (8, 3), (5, 128)]
    (codeMat 106) (codeMat 141) (codeMat 226) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane491GenSource0268 :
    QuotientRankAtLeast (spanCodes [274, 144, 82, 51, 11, 6]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 164, 96, 16, 10, 1] [(274, 223), (144, 27), (82, 222), (51, 352), (11, 368), (6, 256)]
    (codeMat 84) (codeMat 382) (codeMat 499) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit69_lb15_unconditional

theorem plane491GenSource0269 :
    QuotientRankAtLeast (spanCodes [274, 145, 82, 50, 11, 6]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(274, 420), (145, 446), (82, 447), (50, 160), (11, 496), (6, 16)]
    (codeMat 205) (codeMat 473) (codeMat 409) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

end QiushiMatmul
