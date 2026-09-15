import QiushiPlane475GenData
import QiushiCertifiedTransport
import QiushiOrbit10FP
import QiushiOrbit11FP
import QiushiOrbit14FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane475GenSource0110 :
    QuotientRankAtLeast (spanCodes [257, 129, 66, 34, 19, 10, 6]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(257, 23), (129, 30), (66, 29), (34, 503), (19, 414), (10, 373), (6, 8)]
    (codeMat 461) (codeMat 501) (codeMat 494) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane475GenSource0111 :
    QuotientRankAtLeast (spanCodes [258, 131, 67, 35, 18, 10, 5]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(258, 483), (131, 126), (67, 119), (35, 97), (18, 511), (10, 503), (5, 130)]
    (codeMat 470) (codeMat 474) (codeMat 395) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane475GenSource0112 :
    QuotientRankAtLeast (spanCodes [261, 128, 69, 37, 20, 8, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(261, 21), (128, 1), (69, 23), (37, 381), (20, 97), (8, 511), (2, 8)]
    (codeMat 460) (codeMat 335) (codeMat 426) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane475GenSource0113 :
    QuotientRankAtLeast (spanCodes [288, 160, 96, 16, 9, 5, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(288, 325), (160, 324), (96, 326), (16, 256), (9, 432), (5, 24), (3, 16)]
    (codeMat 140) (codeMat 460) (codeMat 122) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane475GenSource0114 :
    QuotientRankAtLeast (spanCodes [258, 131, 67, 35, 19, 10, 5]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(258, 483), (131, 413), (67, 245), (35, 97), (19, 414), (10, 373), (5, 130)]
    (codeMat 478) (codeMat 346) (codeMat 459) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane475GenSource0115 :
    QuotientRankAtLeast (spanCodes [256, 130, 66, 34, 16, 10, 5]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(256, 32), (130, 216), (66, 240), (34, 196), (16, 3), (10, 198), (5, 128)]
    (codeMat 98) (codeMat 346) (codeMat 459) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane475GenSource0116 :
    QuotientRankAtLeast (spanCodes [258, 128, 64, 32, 16, 10, 5]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(258, 100), (128, 9), (64, 54), (32, 32), (16, 8), (10, 112), (5, 128)]
    (codeMat 86) (codeMat 330) (codeMat 394) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane475GenSource0117 :
    QuotientRankAtLeast (spanCodes [288, 161, 96, 16, 9, 4, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(288, 3), (161, 500), (96, 326), (16, 256), (9, 432), (4, 24), (3, 16)]
    (codeMat 142) (codeMat 236) (codeMat 123) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane475GenSource0118 :
    QuotientRankAtLeast (spanCodes [258, 130, 70, 38, 18, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(258, 327), (130, 2), (70, 68), (38, 184), (18, 16), (10, 416), (1, 256)]
    (codeMat 93) (codeMat 372) (codeMat 93) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane475GenSource0119 :
    QuotientRankAtLeast (spanCodes [274, 128, 66, 34, 10, 6, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(274, 238), (128, 325), (66, 170), (34, 424), (10, 168), (6, 24), (1, 16)]
    (codeMat 142) (codeMat 426) (codeMat 335) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

end QiushiMatmul
