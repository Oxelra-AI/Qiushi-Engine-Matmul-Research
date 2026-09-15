import QiushiPlane490GenData
import QiushiCertifiedTransport
import QiushiOrbit10FP
import QiushiOrbit11FP
import QiushiOrbit14FP
import QiushiOrbit25FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane490GenSource0470 :
    QuotientRankAtLeast (spanCodes [256, 160, 96, 17, 8, 4, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 2), (160, 148), (96, 149), (17, 96), (8, 360), (4, 128), (2, 256)]
    (codeMat 92) (codeMat 225) (codeMat 169) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane490GenSource0471 :
    QuotientRankAtLeast (spanCodes [256, 130, 64, 18, 10, 6, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(256, 54), (130, 3), (64, 9), (18, 216), (10, 88), (6, 40), (1, 8)]
    (codeMat 141) (codeMat 307) (codeMat 311) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane490GenSource0472 :
    QuotientRankAtLeast (spanCodes [260, 132, 68, 20, 8, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(260, 54), (132, 30), (68, 22), (20, 198), (8, 128), (2, 3), (1, 2)]
    (codeMat 161) (codeMat 314) (codeMat 271) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane490GenSource0473 :
    QuotientRankAtLeast (spanCodes [274, 144, 66, 48, 10, 6, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(274, 180), (144, 32), (66, 76), (48, 128), (10, 68), (6, 2), (1, 1)]
    (codeMat 177) (codeMat 417) (codeMat 177) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane490GenSource0474 :
    QuotientRankAtLeast (spanCodes [274, 144, 64, 50, 10, 6, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(274, 101), (144, 40), (64, 216), (50, 69), (10, 197), (6, 1), (1, 3)]
    (codeMat 177) (codeMat 395) (codeMat 474) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane490GenSource0475 :
    QuotientRankAtLeast (spanCodes [274, 146, 66, 50, 10, 6, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(274, 231), (146, 63), (66, 79), (50, 199), (10, 71), (6, 3), (1, 1)]
    (codeMat 177) (codeMat 403) (codeMat 403) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane490GenSource0476 :
    QuotientRankAtLeast (spanCodes [275, 144, 67, 50, 10, 7]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 4, 8, 80, 256] [(275, 93), (144, 256), (67, 347), (50, 336), (10, 338), (7, 5)]
    (codeMat 407) (codeMat 425) (codeMat 249) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit25_lb12

theorem plane490GenSource0477 :
    QuotientRankAtLeast (spanCodes [275, 146, 65, 50, 10, 7]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 4, 8, 80, 256] [(275, 266), (146, 8), (65, 260), (50, 336), (10, 341), (7, 2)]
    (codeMat 335) (codeMat 369) (codeMat 377) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit25_lb12

theorem plane490GenSource0478 :
    QuotientRankAtLeast (spanCodes [273, 144, 80, 33, 8, 5, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(273, 486), (144, 1), (80, 324), (33, 416), (8, 256), (5, 16), (2, 8)]
    (codeMat 142) (codeMat 354) (codeMat 142) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane490GenSource0479 :
    QuotientRankAtLeast (spanCodes [273, 145, 65, 49, 8, 5, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(273, 230), (145, 61), (65, 130), (49, 208), (8, 128), (5, 32), (2, 40)]
    (codeMat 143) (codeMat 426) (codeMat 335) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

end QiushiMatmul
