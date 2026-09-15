import QiushiPlane466GenData
import QiushiCertifiedTransport
import QiushiOrbit10FP
import QiushiOrbit11FP
import QiushiOrbit14FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane466GenSource0180 :
    QuotientRankAtLeast (spanCodes [256, 132, 68, 37, 20, 9, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 3), (132, 30), (68, 31), (37, 227), (20, 414), (9, 511), (3, 8)]
    (codeMat 396) (codeMat 253) (codeMat 415) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane466GenSource0181 :
    QuotientRankAtLeast (spanCodes [260, 128, 68, 33, 20, 9, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(260, 511), (128, 3), (68, 510), (33, 392), (20, 480), (9, 384), (3, 360)]
    (codeMat 212) (codeMat 382) (codeMat 499) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane466GenSource0182 :
    QuotientRankAtLeast (spanCodes [260, 128, 68, 37, 16, 9, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(260, 511), (128, 1), (68, 508), (37, 224), (16, 8), (9, 256), (3, 360)]
    (codeMat 212) (codeMat 358) (codeMat 158) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane466GenSource0183 :
    QuotientRankAtLeast (spanCodes [259, 130, 67, 35, 17, 10, 7]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(259, 136), (130, 256), (67, 480), (35, 10), (17, 28), (10, 31), (7, 8)]
    (codeMat 331) (codeMat 233) (codeMat 233) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane466GenSource0184 :
    QuotientRankAtLeast (spanCodes [259, 130, 67, 34, 16, 10, 7]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(259, 160), (130, 8), (67, 120), (34, 68), (16, 1), (10, 71), (7, 128)]
    (codeMat 106) (codeMat 331) (codeMat 410) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane466GenSource0185 :
    QuotientRankAtLeast (spanCodes [258, 130, 66, 35, 16, 10, 6]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(258, 129), (130, 1), (66, 257), (35, 284), (16, 8), (10, 105), (6, 130)]
    (codeMat 277) (codeMat 103) (codeMat 188) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane466GenSource0186 :
    QuotientRankAtLeast (spanCodes [258, 129, 65, 33, 18, 10, 5]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(258, 100), (129, 237), (65, 54), (33, 160), (18, 40), (10, 240), (5, 128)]
    (codeMat 94) (codeMat 458) (codeMat 458) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane466GenSource0187 :
    QuotientRankAtLeast (spanCodes [256, 130, 64, 34, 19, 10, 4]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 2), (130, 384), (64, 3), (34, 406), (19, 373), (10, 414), (4, 130)]
    (codeMat 340) (codeMat 185) (codeMat 481) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane466GenSource0188 :
    QuotientRankAtLeast (spanCodes [257, 131, 64, 34, 18, 10, 4]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(257, 68), (131, 326), (64, 325), (34, 416), (18, 432), (10, 424), (4, 256)]
    (codeMat 85) (codeMat 465) (codeMat 465) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane466GenSource0189 :
    QuotientRankAtLeast (spanCodes [258, 128, 64, 33, 18, 10, 4]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(258, 149), (128, 2), (64, 3), (33, 227), (18, 130), (10, 138), (4, 511)]
    (codeMat 468) (codeMat 317) (codeMat 285) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

end QiushiMatmul
