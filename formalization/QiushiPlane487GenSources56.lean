import QiushiPlane487GenData
import QiushiCertifiedTransport
import QiushiOrbit10FP
import QiushiOrbit11FP
import QiushiOrbit14FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane487GenSource0560 :
    QuotientRankAtLeast (spanCodes [256, 131, 64, 33, 18, 10, 6]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(256, 54), (131, 228), (64, 63), (33, 112), (18, 32), (10, 248), (6, 128)]
    (codeMat 95) (codeMat 489) (codeMat 241) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane487GenSource0561 :
    QuotientRankAtLeast (spanCodes [258, 131, 65, 34, 18, 10, 7]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(258, 23), (131, 29), (65, 3), (34, 488), (18, 360), (10, 232), (7, 8)]
    (codeMat 141) (codeMat 431) (codeMat 477) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane487GenSource0562 :
    QuotientRankAtLeast (spanCodes [259, 131, 65, 35, 18, 10, 7]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(259, 488), (131, 480), (65, 256), (35, 362), (18, 3), (10, 508), (7, 360)]
    (codeMat 355) (codeMat 114) (codeMat 204) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane487GenSource0563 :
    QuotientRankAtLeast (spanCodes [256, 128, 65, 35, 18, 10, 7]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(256, 2), (128, 3), (65, 325), (35, 272), (18, 24), (10, 424), (7, 256)]
    (codeMat 92) (codeMat 115) (codeMat 492) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane487GenSource0564 :
    QuotientRankAtLeast (spanCodes [259, 131, 64, 34, 19, 10, 7]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(259, 386), (131, 387), (64, 3), (34, 97), (19, 235), (10, 414), (7, 130)]
    (codeMat 348) (codeMat 395) (codeMat 474) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane487GenSource0565 :
    QuotientRankAtLeast (spanCodes [258, 130, 66, 32, 17, 10, 7]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(258, 326), (130, 325), (66, 327), (32, 432), (17, 168), (10, 184), (7, 256)]
    (codeMat 92) (codeMat 491) (codeMat 375) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane487GenSource0566 :
    QuotientRankAtLeast (spanCodes [259, 129, 66, 34, 18, 10, 4]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(259, 324), (129, 70), (66, 71), (34, 416), (18, 432), (10, 440), (4, 256)]
    (codeMat 85) (codeMat 473) (codeMat 409) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane487GenSource0567 :
    QuotientRankAtLeast (spanCodes [257, 128, 66, 33, 18, 10, 4]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(257, 404), (128, 9), (66, 119), (33, 276), (18, 8), (10, 503), (4, 130)]
    (codeMat 415) (codeMat 106) (codeMat 396) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane487GenSource0568 :
    QuotientRankAtLeast (spanCodes [256, 129, 66, 33, 18, 10, 4]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 9), (129, 23), (66, 21), (33, 105), (18, 511), (10, 381), (4, 8)]
    (codeMat 461) (codeMat 215) (codeMat 342) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane487GenSource0569 :
    QuotientRankAtLeast (spanCodes [258, 128, 64, 32, 16, 10, 4]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(258, 80), (128, 8), (64, 32), (32, 2), (16, 1), (10, 68), (4, 128)]
    (codeMat 98) (codeMat 98) (codeMat 140) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

end QiushiMatmul
