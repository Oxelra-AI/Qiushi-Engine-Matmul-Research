import QiushiPlane471GenData
import QiushiCertifiedTransport
import QiushiOrbit10FP
import QiushiOrbit11FP
import QiushiOrbit14FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane471GenSource0230 :
    QuotientRankAtLeast (spanCodes [288, 160, 68, 16, 8, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(288, 325), (160, 69), (68, 168), (16, 1), (8, 2), (2, 8), (1, 16)]
    (codeMat 266) (codeMat 270) (codeMat 298) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane471GenSource0231 :
    QuotientRankAtLeast (spanCodes [256, 130, 67, 33, 19, 10, 4]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 9), (130, 3), (67, 29), (33, 97), (19, 235), (10, 373), (4, 8)]
    (codeMat 397) (codeMat 87) (codeMat 468) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane471GenSource0232 :
    QuotientRankAtLeast (spanCodes [257, 130, 66, 32, 19, 10, 5]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(257, 510), (130, 3), (66, 363), (32, 8), (19, 373), (10, 235), (5, 511)]
    (codeMat 405) (codeMat 94) (codeMat 500) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane471GenSource0233 :
    QuotientRankAtLeast (spanCodes [259, 128, 66, 34, 16, 10, 6]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(259, 97), (128, 130), (66, 276), (34, 151), (16, 2), (10, 148), (6, 511)]
    (codeMat 426) (codeMat 348) (codeMat 125) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane471GenSource0234 :
    QuotientRankAtLeast (spanCodes [256, 130, 67, 33, 17, 10, 6]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 360), (130, 256), (67, 480), (33, 21), (17, 28), (10, 31), (6, 8)]
    (codeMat 331) (codeMat 461) (codeMat 234) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane471GenSource0235 :
    QuotientRankAtLeast (spanCodes [259, 130, 65, 34, 16, 10, 5]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(259, 240), (130, 8), (65, 32), (34, 70), (16, 1), (10, 68), (5, 128)]
    (codeMat 106) (codeMat 354) (codeMat 142) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane471GenSource0236 :
    QuotientRankAtLeast (spanCodes [256, 130, 66, 33, 19, 10, 5]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 1), (130, 360), (66, 363), (33, 503), (19, 414), (10, 235), (5, 511)]
    (codeMat 412) (codeMat 206) (codeMat 498) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane471GenSource0237 :
    QuotientRankAtLeast (spanCodes [256, 131, 67, 33, 19, 10, 4]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 1), (131, 30), (67, 29), (33, 105), (19, 414), (10, 373), (4, 8)]
    (codeMat 396) (codeMat 213) (codeMat 470) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane471GenSource0238 :
    QuotientRankAtLeast (spanCodes [258, 128, 66, 35, 18, 10, 4]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(258, 68), (128, 1), (66, 71), (35, 160), (18, 8), (10, 440), (4, 256)]
    (codeMat 92) (codeMat 331) (codeMat 410) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane471GenSource0239 :
    QuotientRankAtLeast (spanCodes [257, 130, 67, 32, 16, 10, 7]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(257, 196), (130, 1), (67, 71), (32, 32), (16, 8), (10, 120), (7, 128)]
    (codeMat 85) (codeMat 331) (codeMat 410) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

end QiushiMatmul
