import QiushiPlane487GenData
import QiushiCertifiedTransport
import QiushiOrbit10FP
import QiushiOrbit11FP
import QiushiOrbit14FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane487GenSource0540 :
    QuotientRankAtLeast (spanCodes [257, 128, 67, 35, 18, 10, 5]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(257, 255), (128, 9), (67, 137), (35, 406), (18, 8), (10, 138), (5, 511)]
    (codeMat 351) (codeMat 267) (codeMat 282) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane487GenSource0541 :
    QuotientRankAtLeast (spanCodes [257, 130, 64, 34, 16, 10, 4]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(257, 68), (130, 2), (64, 325), (34, 160), (16, 16), (10, 168), (4, 256)]
    (codeMat 85) (codeMat 337) (codeMat 337) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane487GenSource0542 :
    QuotientRankAtLeast (spanCodes [257, 128, 65, 33, 18, 10, 7]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(257, 387), (128, 1), (65, 384), (33, 235), (18, 8), (10, 503), (7, 130)]
    (codeMat 348) (codeMat 334) (codeMat 442) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane487GenSource0543 :
    QuotientRankAtLeast (spanCodes [259, 128, 67, 33, 17, 10, 6]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(259, 240), (128, 32), (67, 248), (33, 70), (17, 196), (10, 199), (6, 128)]
    (codeMat 99) (codeMat 489) (codeMat 241) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane487GenSource0544 :
    QuotientRankAtLeast (spanCodes [256, 131, 67, 33, 17, 10, 6]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(256, 32), (131, 112), (67, 120), (33, 196), (17, 70), (10, 71), (6, 128)]
    (codeMat 99) (codeMat 473) (codeMat 409) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane487GenSource0545 :
    QuotientRankAtLeast (spanCodes [259, 131, 67, 34, 17, 10, 6]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(259, 68), (131, 70), (67, 71), (34, 160), (17, 112), (10, 120), (6, 128)]
    (codeMat 92) (codeMat 473) (codeMat 409) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane487GenSource0546 :
    QuotientRankAtLeast (spanCodes [258, 131, 64, 32, 18, 10, 6]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(258, 258), (131, 326), (64, 325), (32, 16), (18, 432), (10, 424), (6, 256)]
    (codeMat 85) (codeMat 241) (codeMat 489) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane487GenSource0547 :
    QuotientRankAtLeast (spanCodes [256, 134, 70, 32, 18, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(256, 3), (134, 326), (70, 324), (32, 24), (18, 432), (10, 416), (1, 256)]
    (codeMat 84) (codeMat 244) (codeMat 95) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane487GenSource0548 :
    QuotientRankAtLeast (spanCodes [262, 128, 70, 32, 18, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(262, 510), (128, 1), (70, 509), (32, 384), (18, 8), (10, 264), (1, 360)]
    (codeMat 156) (codeMat 355) (codeMat 190) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane487GenSource0549 :
    QuotientRankAtLeast (spanCodes [262, 130, 70, 34, 18, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(262, 119), (130, 9), (70, 245), (34, 392), (18, 8), (10, 264), (1, 360)]
    (codeMat 158) (codeMat 359) (codeMat 174) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

end QiushiMatmul
