import QiushiPlane491GenData
import QiushiCertifiedTransport
import QiushiOrbit10FP
import QiushiOrbit11FP
import QiushiOrbit14FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane491GenSource0580 :
    QuotientRankAtLeast (spanCodes [257, 130, 67, 33, 18, 10, 5]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(257, 259), (130, 1), (67, 71), (33, 280), (18, 8), (10, 440), (5, 256)]
    (codeMat 93) (codeMat 111) (codeMat 412) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane491GenSource0581 :
    QuotientRankAtLeast (spanCodes [258, 128, 65, 35, 17, 9, 4]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(258, 68), (128, 325), (65, 3), (35, 160), (17, 424), (9, 24), (4, 256)]
    (codeMat 93) (codeMat 395) (codeMat 474) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane491GenSource0582 :
    QuotientRankAtLeast (spanCodes [257, 130, 65, 33, 17, 8, 4]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(257, 210), (130, 54), (65, 9), (33, 80), (17, 112), (8, 8), (4, 128)]
    (codeMat 87) (codeMat 177) (codeMat 417) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane491GenSource0583 :
    QuotientRankAtLeast (spanCodes [258, 128, 64, 35, 16, 8, 4]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(258, 68), (128, 1), (64, 3), (35, 160), (16, 8), (8, 24), (4, 256)]
    (codeMat 84) (codeMat 267) (codeMat 282) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane491GenSource0584 :
    QuotientRankAtLeast (spanCodes [258, 128, 67, 35, 19, 11, 4]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(258, 68), (128, 325), (67, 327), (35, 160), (19, 168), (11, 184), (4, 256)]
    (codeMat 85) (codeMat 459) (codeMat 346) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane491GenSource0585 :
    QuotientRankAtLeast (spanCodes [258, 128, 66, 35, 18, 10, 4]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(258, 68), (128, 1), (66, 71), (35, 160), (18, 8), (10, 440), (4, 256)]
    (codeMat 92) (codeMat 331) (codeMat 410) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane491GenSource0586 :
    QuotientRankAtLeast (spanCodes [259, 129, 66, 34, 18, 10, 4]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(259, 324), (129, 70), (66, 71), (34, 416), (18, 432), (10, 440), (4, 256)]
    (codeMat 85) (codeMat 473) (codeMat 409) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane491GenSource0587 :
    QuotientRankAtLeast (spanCodes [258, 131, 66, 32, 17, 9, 7]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(258, 97), (131, 235), (66, 414), (32, 256), (17, 387), (9, 3), (7, 130)]
    (codeMat 171) (codeMat 395) (codeMat 474) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane491GenSource0588 :
    QuotientRankAtLeast (spanCodes [256, 131, 64, 32, 19, 9, 7]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 2), (131, 361), (64, 1), (32, 130), (19, 105), (9, 8), (7, 511)]
    (codeMat 412) (codeMat 161) (codeMat 161) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane491GenSource0589 :
    QuotientRankAtLeast (spanCodes [259, 128, 64, 35, 19, 9, 7]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(259, 352), (128, 384), (64, 128), (35, 361), (19, 150), (9, 2), (7, 360)]
    (codeMat 299) (codeMat 156) (codeMat 102) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

end QiushiMatmul
