import QiushiPlane490GenData
import QiushiCertifiedTransport
import QiushiOrbit10FP
import QiushiOrbit11FP
import QiushiOrbit14FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane490GenSource0570 :
    QuotientRankAtLeast (spanCodes [256, 129, 65, 32, 19, 10, 6]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 1), (129, 363), (65, 360), (32, 8), (19, 235), (10, 414), (6, 511)]
    (codeMat 468) (codeMat 213) (codeMat 470) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane490GenSource0571 :
    QuotientRankAtLeast (spanCodes [256, 130, 66, 32, 19, 10, 6]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 2), (130, 360), (66, 363), (32, 130), (19, 414), (10, 235), (6, 511)]
    (codeMat 412) (codeMat 234) (codeMat 461) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane490GenSource0572 :
    QuotientRankAtLeast (spanCodes [256, 130, 64, 34, 19, 10, 6]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 2), (130, 360), (64, 3), (34, 381), (19, 414), (10, 373), (6, 511)]
    (codeMat 468) (codeMat 171) (codeMat 485) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane490GenSource0573 :
    QuotientRankAtLeast (spanCodes [260, 132, 66, 36, 22, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(260, 9), (132, 353), (66, 404), (36, 8), (22, 97), (10, 406), (1, 130)]
    (codeMat 478) (codeMat 140) (codeMat 98) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane490GenSource0574 :
    QuotientRankAtLeast (spanCodes [274, 128, 66, 50, 10, 4, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(274, 427), (128, 325), (66, 170), (50, 424), (10, 168), (4, 24), (1, 16)]
    (codeMat 142) (codeMat 174) (codeMat 359) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane490GenSource0575 :
    QuotientRankAtLeast (spanCodes [256, 162, 64, 18, 10, 4, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(256, 3), (162, 246), (64, 2), (18, 432), (10, 176), (4, 24), (1, 16)]
    (codeMat 140) (codeMat 188) (codeMat 103) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane490GenSource0576 :
    QuotientRankAtLeast (spanCodes [274, 146, 64, 32, 10, 6, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(274, 508), (146, 511), (64, 2), (32, 256), (10, 184), (6, 24), (1, 16)]
    (codeMat 140) (codeMat 410) (codeMat 331) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane490GenSource0577 :
    QuotientRankAtLeast (spanCodes [257, 128, 65, 35, 18, 10, 6]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(257, 232), (128, 128), (65, 360), (35, 227), (18, 130), (10, 381), (6, 8)]
    (codeMat 271) (codeMat 117) (codeMat 380) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane490GenSource0578 :
    QuotientRankAtLeast (spanCodes [257, 129, 66, 33, 18, 10, 6]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(257, 70), (129, 196), (66, 199), (33, 112), (18, 32), (10, 248), (6, 128)]
    (codeMat 93) (codeMat 489) (codeMat 241) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane490GenSource0579 :
    QuotientRankAtLeast (spanCodes [256, 128, 67, 32, 19, 10, 6]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 1), (128, 3), (67, 387), (32, 8), (19, 414), (10, 235), (6, 130)]
    (codeMat 340) (codeMat 87) (codeMat 468) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

end QiushiMatmul
