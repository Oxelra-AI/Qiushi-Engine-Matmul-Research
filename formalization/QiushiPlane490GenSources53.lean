import QiushiPlane490GenData
import QiushiCertifiedTransport
import QiushiOrbit10FP
import QiushiOrbit11FP
import QiushiOrbit14FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane490GenSource0530 :
    QuotientRankAtLeast (spanCodes [256, 130, 66, 35, 19, 10, 4]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 128), (130, 3), (66, 387), (35, 406), (19, 414), (10, 235), (4, 130)]
    (codeMat 277) (codeMat 115) (codeMat 492) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane490GenSource0531 :
    QuotientRankAtLeast (spanCodes [259, 130, 65, 34, 16, 10, 5]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(259, 240), (130, 8), (65, 32), (34, 70), (16, 1), (10, 68), (5, 128)]
    (codeMat 106) (codeMat 354) (codeMat 142) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane490GenSource0532 :
    QuotientRankAtLeast (spanCodes [257, 131, 64, 32, 18, 10, 5]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(257, 257), (131, 326), (64, 325), (32, 8), (18, 432), (10, 424), (5, 256)]
    (codeMat 85) (codeMat 213) (codeMat 470) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane490GenSource0533 :
    QuotientRankAtLeast (spanCodes [257, 129, 66, 32, 18, 10, 5]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(257, 259), (129, 70), (66, 71), (32, 24), (18, 432), (10, 440), (5, 256)]
    (codeMat 85) (codeMat 253) (codeMat 415) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane490GenSource0534 :
    QuotientRankAtLeast (spanCodes [257, 130, 64, 33, 18, 10, 5]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(257, 257), (130, 3), (64, 325), (33, 264), (18, 24), (10, 424), (5, 256)]
    (codeMat 93) (codeMat 87) (codeMat 468) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane490GenSource0535 :
    QuotientRankAtLeast (spanCodes [257, 131, 65, 33, 18, 10, 5]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(257, 10), (131, 30), (65, 3), (33, 136), (18, 384), (10, 232), (5, 8)]
    (codeMat 205) (codeMat 185) (codeMat 481) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane490GenSource0536 :
    QuotientRankAtLeast (spanCodes [257, 131, 66, 34, 18, 10, 5]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(257, 381), (131, 414), (66, 235), (34, 259), (18, 3), (10, 387), (5, 130)]
    (codeMat 163) (codeMat 375) (codeMat 491) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane490GenSource0537 :
    QuotientRankAtLeast (spanCodes [256, 130, 64, 32, 19, 10, 5]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 1), (130, 384), (64, 3), (32, 8), (19, 373), (10, 414), (5, 130)]
    (codeMat 340) (codeMat 157) (codeMat 486) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane490GenSource0538 :
    QuotientRankAtLeast (spanCodes [256, 131, 65, 32, 19, 10, 5]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 9), (131, 374), (65, 384), (32, 8), (19, 373), (10, 235), (5, 511)]
    (codeMat 342) (codeMat 94) (codeMat 500) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane490GenSource0539 :
    QuotientRankAtLeast (spanCodes [256, 128, 67, 33, 19, 10, 5]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 128), (128, 384), (67, 232), (33, 138), (19, 414), (10, 235), (5, 8)]
    (codeMat 271) (codeMat 185) (codeMat 481) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

end QiushiMatmul
