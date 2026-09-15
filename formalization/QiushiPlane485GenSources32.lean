import QiushiPlane485GenData
import QiushiCertifiedTransport
import QiushiOrbit10FP
import QiushiOrbit11FP
import QiushiOrbit14FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane485GenSource0320 :
    QuotientRankAtLeast (spanCodes [256, 130, 64, 32, 18, 10, 6]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(256, 9), (130, 219), (64, 54), (32, 8), (18, 216), (10, 240), (6, 128)]
    (codeMat 86) (codeMat 94) (codeMat 500) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane485GenSource0321 :
    QuotientRankAtLeast (spanCodes [256, 128, 66, 32, 18, 10, 6]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(256, 1), (128, 3), (66, 198), (32, 8), (18, 216), (10, 240), (6, 128)]
    (codeMat 84) (codeMat 94) (codeMat 500) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane485GenSource0322 :
    QuotientRankAtLeast (spanCodes [258, 130, 64, 35, 19, 10, 7]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(258, 385), (130, 384), (64, 3), (35, 381), (19, 373), (10, 414), (7, 130)]
    (codeMat 340) (codeMat 445) (codeMat 478) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane485GenSource0323 :
    QuotientRankAtLeast (spanCodes [258, 131, 65, 35, 19, 10, 7]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(258, 23), (131, 29), (65, 3), (35, 503), (19, 373), (10, 235), (7, 8)]
    (codeMat 461) (codeMat 431) (codeMat 477) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane485GenSource0324 :
    QuotientRankAtLeast (spanCodes [256, 130, 66, 35, 19, 10, 7]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 1), (130, 384), (66, 387), (35, 138), (19, 373), (10, 235), (7, 130)]
    (codeMat 348) (codeMat 213) (codeMat 470) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane485GenSource0325 :
    QuotientRankAtLeast (spanCodes [256, 131, 67, 33, 16, 10, 4]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 1), (131, 31), (67, 28), (33, 105), (16, 511), (10, 284), (4, 8)]
    (codeMat 460) (codeMat 214) (codeMat 214) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane485GenSource0326 :
    QuotientRankAtLeast (spanCodes [258, 130, 65, 32, 16, 10, 4]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(258, 208), (130, 8), (65, 32), (32, 2), (16, 1), (10, 68), (4, 128)]
    (codeMat 106) (codeMat 98) (codeMat 140) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane485GenSource0327 :
    QuotientRankAtLeast (spanCodes [258, 128, 67, 32, 16, 10, 4]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(258, 80), (128, 216), (67, 240), (32, 2), (16, 3), (10, 198), (4, 128)]
    (codeMat 106) (codeMat 122) (codeMat 460) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane485GenSource0328 :
    QuotientRankAtLeast (spanCodes [257, 130, 64, 34, 16, 10, 4]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(257, 68), (130, 2), (64, 325), (34, 160), (16, 16), (10, 168), (4, 256)]
    (codeMat 85) (codeMat 337) (codeMat 337) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane485GenSource0329 :
    QuotientRankAtLeast (spanCodes [256, 129, 66, 34, 16, 10, 4]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 9), (129, 28), (66, 31), (34, 96), (16, 256), (10, 480), (4, 8)]
    (codeMat 141) (codeMat 205) (codeMat 242) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

end QiushiMatmul
