import QiushiPlane490GenData
import QiushiCertifiedTransport
import QiushiMonoOrbit74From17
import QiushiOrbit35FP
import QiushiStep99Orbit55Dispatch
import QiushiStep99Orbit65Dispatch
import QiushiStep99Orbit69Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane490GenSource0390 :
    QuotientRankAtLeast (spanCodes [258, 128, 64, 38, 17, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(258, 96), (128, 8), (64, 9), (38, 224), (17, 28), (10, 31)]
    (codeMat 124) (codeMat 281) (codeMat 281) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane490GenSource0391 :
    QuotientRankAtLeast (spanCodes [257, 194, 32, 18, 10, 7]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(257, 252), (194, 224), (32, 9), (18, 128), (10, 136), (7, 3)]
    (codeMat 282) (codeMat 236) (codeMat 123) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane490GenSource0392 :
    QuotientRankAtLeast (spanCodes [275, 144, 83, 50, 10, 6]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(275, 286), (144, 260), (83, 287), (50, 160), (10, 480), (6, 16)]
    (codeMat 140) (codeMat 489) (codeMat 241) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

theorem plane490GenSource0393 :
    QuotientRankAtLeast (spanCodes [275, 128, 81, 35, 10, 5]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(275, 171), (128, 320), (81, 238), (35, 507), (10, 437), (5, 1)]
    (codeMat 305) (codeMat 494) (codeMat 501) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

theorem plane490GenSource0394 :
    QuotientRankAtLeast (spanCodes [256, 129, 96, 19, 10, 5]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 164, 96, 16, 10, 1] [(256, 256), (129, 112), (96, 164), (19, 113), (10, 446), (5, 16)]
    (codeMat 271) (codeMat 330) (codeMat 394) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit69_lb15_unconditional

theorem plane490GenSource0395 :
    QuotientRankAtLeast (spanCodes [258, 194, 32, 17, 10, 4]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(258, 96), (194, 224), (32, 9), (17, 28), (10, 31), (4, 8)]
    (codeMat 267) (codeMat 205) (codeMat 242) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane490GenSource0396 :
    QuotientRankAtLeast (spanCodes [272, 145, 64, 37, 9, 3]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(272, 252), (145, 131), (64, 9), (37, 96), (9, 8), (3, 128)]
    (codeMat 95) (codeMat 275) (codeMat 275) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane490GenSource0397 :
    QuotientRankAtLeast (spanCodes [272, 193, 49, 9, 4, 3]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(272, 252), (193, 96), (49, 131), (9, 128), (4, 9), (3, 8)]
    (codeMat 281) (codeMat 244) (codeMat 95) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane490GenSource0398 :
    QuotientRankAtLeast (spanCodes [260, 68, 32, 22, 10, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 132, 32, 12, 2, 1] [(260, 1), (68, 44), (32, 2), (22, 436), (10, 304), (1, 32)]
    (codeMat 85) (codeMat 156) (codeMat 102) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit55_lb14_unconditional

theorem plane490GenSource0399 :
    QuotientRankAtLeast (spanCodes [257, 65, 33, 18, 10, 7]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [324, 192, 32, 20, 10, 1] [(257, 368), (65, 432), (33, 53), (18, 63), (10, 62), (7, 32)]
    (codeMat 266) (codeMat 478) (codeMat 445) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit74_lb14_mono

end QiushiMatmul
