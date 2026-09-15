import QiushiPlane489GenData
import QiushiCertifiedTransport
import QiushiOrbit10FP
import QiushiOrbit11FP
import QiushiOrbit14FP
import QiushiOrbit25FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane489GenSource0320 :
    QuotientRankAtLeast (spanCodes [258, 129, 67, 33, 18, 10, 6]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(258, 503), (129, 414), (67, 235), (33, 480), (18, 384), (10, 232), (6, 8)]
    (codeMat 207) (codeMat 445) (codeMat 478) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane489GenSource0321 :
    QuotientRankAtLeast (spanCodes [258, 128, 66, 33, 18, 10, 6]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(258, 69), (128, 1), (66, 71), (33, 168), (18, 8), (10, 440), (6, 256)]
    (codeMat 92) (codeMat 335) (codeMat 426) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane489GenSource0322 :
    QuotientRankAtLeast (spanCodes [258, 129, 66, 32, 18, 10, 6]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(258, 258), (129, 70), (66, 71), (32, 16), (18, 432), (10, 440), (6, 256)]
    (codeMat 85) (codeMat 249) (codeMat 425) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane489GenSource0323 :
    QuotientRankAtLeast (spanCodes [258, 146, 66, 34, 10, 5]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 4, 8, 80, 256] [(258, 344), (146, 256), (66, 347), (34, 336), (10, 338), (5, 5)]
    (codeMat 470) (codeMat 169) (codeMat 225) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit25_lb12

theorem plane489GenSource0324 :
    QuotientRankAtLeast (spanCodes [258, 130, 66, 33, 19, 10, 5]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(258, 259), (130, 3), (66, 387), (33, 381), (19, 414), (10, 235), (5, 130)]
    (codeMat 277) (codeMat 375) (codeMat 491) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane489GenSource0325 :
    QuotientRankAtLeast (spanCodes [258, 130, 65, 35, 18, 10, 5]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(258, 361), (130, 1), (65, 3), (35, 406), (18, 8), (10, 138), (5, 511)]
    (codeMat 477) (codeMat 267) (codeMat 282) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane489GenSource0326 :
    QuotientRankAtLeast (spanCodes [258, 131, 65, 34, 18, 10, 5]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(258, 235), (131, 284), (65, 511), (34, 387), (18, 3), (10, 259), (5, 130)]
    (codeMat 163) (codeMat 351) (codeMat 239) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane489GenSource0327 :
    QuotientRankAtLeast (spanCodes [258, 130, 67, 33, 18, 10, 5]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(258, 138), (130, 8), (67, 105), (33, 508), (18, 1), (10, 361), (5, 511)]
    (codeMat 491) (codeMat 102) (codeMat 156) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane489GenSource0328 :
    QuotientRankAtLeast (spanCodes [258, 131, 67, 32, 18, 10, 5]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(258, 373), (131, 97), (67, 105), (32, 3), (18, 360), (10, 361), (5, 511)]
    (codeMat 482) (codeMat 230) (codeMat 159) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane489GenSource0329 :
    QuotientRankAtLeast (spanCodes [258, 128, 64, 34, 16, 10, 5]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(258, 112), (128, 8), (64, 32), (34, 70), (16, 1), (10, 68), (5, 128)]
    (codeMat 98) (codeMat 354) (codeMat 142) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

end QiushiMatmul
