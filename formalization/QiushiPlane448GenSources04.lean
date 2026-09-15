import QiushiPlane448GenData
import QiushiCertifiedTransport
import QiushiMonoOrbit112From35T
import QiushiMonoOrbit149From65
import QiushiMonoOrbit188From76
import QiushiOrbit10FP
import QiushiStep99Orbit55Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane448GenSource0040 :
    QuotientRankAtLeast (spanCodes [294, 160, 18, 14, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [274, 128, 32, 10, 1] [(294, 434), (160, 306), (18, 32), (14, 11), (1, 1)]
    (codeMat 345) (codeMat 417) (codeMat 177) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit188_lb15_mono

theorem plane448GenSource0041 :
    QuotientRankAtLeast (spanCodes [292, 160, 72, 30, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 96, 8, 2, 1] [(292, 9), (160, 371), (72, 3), (30, 272), (1, 2)]
    (codeMat 207) (codeMat 167) (codeMat 167) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit112_lb15_mono

theorem plane448GenSource0042 :
    QuotientRankAtLeast (spanCodes [314, 160, 82, 4, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 96, 8, 2, 1] [(314, 273), (160, 378), (82, 280), (4, 2), (1, 3)]
    (codeMat 249) (codeMat 187) (codeMat 229) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit112_lb15_mono

theorem plane448GenSource0043 :
    QuotientRankAtLeast (spanCodes [292, 160, 68, 30, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [274, 128, 32, 10, 1] [(292, 128), (160, 170), (68, 10), (30, 435), (1, 1)]
    (codeMat 481) (codeMat 179) (codeMat 421) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit188_lb15_mono

theorem plane448GenSource0044 :
    QuotientRankAtLeast (spanCodes [288, 160, 70, 26, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 68, 16, 10, 1] [(288, 27), (160, 350), (70, 68), (26, 272), (1, 256)]
    (codeMat 93) (codeMat 244) (codeMat 95) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit149_lb15_mono

theorem plane448GenSource0045 :
    QuotientRankAtLeast (spanCodes [314, 160, 90, 6, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 96, 8, 2, 1] [(314, 106), (160, 371), (90, 272), (6, 3), (1, 2)]
    (codeMat 233) (codeMat 412) (codeMat 111) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit112_lb15_mono

theorem plane448GenSource0046 :
    QuotientRankAtLeast (spanCodes [290, 160, 18, 10, 6, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 132, 32, 12, 2, 1] [(290, 436), (160, 306), (18, 32), (10, 13), (6, 2), (1, 1)]
    (codeMat 345) (codeMat 417) (codeMat 177) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit55_lb14_unconditional

theorem plane448GenSource0047 :
    QuotientRankAtLeast (spanCodes [294, 160, 70, 18, 14, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 132, 32, 12, 2, 1] [(294, 138), (160, 170), (70, 13), (18, 438), (14, 15), (1, 1)]
    (codeMat 369) (codeMat 407) (codeMat 405) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit55_lb14_unconditional

theorem plane448GenSource0048 :
    QuotientRankAtLeast (spanCodes [270, 140, 74, 44, 24, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 132, 32, 12, 2, 1] [(270, 165), (140, 285), (74, 274), (44, 437), (24, 45), (1, 438)]
    (codeMat 501) (codeMat 489) (codeMat 241) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit55_lb14_unconditional

theorem plane448GenSource0049 :
    QuotientRankAtLeast (spanCodes [274, 128, 66, 32, 8, 4, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(274, 228), (128, 256), (66, 160), (32, 3), (8, 2), (4, 24), (1, 16)]
    (codeMat 266) (codeMat 172) (codeMat 99) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

end QiushiMatmul
