import QiushiPlane487GenData
import QiushiCertifiedTransport
import QiushiOrbit10FP
import QiushiOrbit11FP
import QiushiOrbit14FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane487GenSource0520 :
    QuotientRankAtLeast (spanCodes [259, 128, 65, 34, 16, 10, 5]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(259, 112), (128, 216), (65, 32), (34, 198), (16, 3), (10, 196), (5, 128)]
    (codeMat 106) (codeMat 370) (codeMat 207) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane487GenSource0521 :
    QuotientRankAtLeast (spanCodes [256, 131, 67, 32, 18, 10, 5]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(256, 3), (131, 70), (67, 71), (32, 24), (18, 432), (10, 440), (5, 256)]
    (codeMat 84) (codeMat 253) (codeMat 415) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane487GenSource0522 :
    QuotientRankAtLeast (spanCodes [259, 131, 67, 35, 18, 10, 5]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(259, 20), (131, 23), (67, 21), (35, 276), (18, 511), (10, 381), (5, 8)]
    (codeMat 396) (codeMat 467) (codeMat 339) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane487GenSource0523 :
    QuotientRankAtLeast (spanCodes [258, 128, 66, 32, 16, 10, 6]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(258, 88), (128, 8), (66, 112), (32, 3), (16, 1), (10, 70), (6, 128)]
    (codeMat 98) (codeMat 110) (codeMat 444) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane487GenSource0524 :
    QuotientRankAtLeast (spanCodes [256, 128, 66, 34, 16, 10, 6]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(256, 3), (128, 1), (66, 70), (34, 88), (16, 8), (10, 112), (6, 128)]
    (codeMat 84) (codeMat 110) (codeMat 444) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane487GenSource0525 :
    QuotientRankAtLeast (spanCodes [257, 129, 64, 32, 18, 10, 6]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(257, 28), (129, 29), (64, 3), (32, 256), (18, 360), (10, 232), (6, 8)]
    (codeMat 140) (codeMat 395) (codeMat 474) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane487GenSource0526 :
    QuotientRankAtLeast (spanCodes [259, 130, 64, 33, 18, 10, 6]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(259, 71), (130, 3), (64, 325), (33, 184), (18, 24), (10, 424), (6, 256)]
    (codeMat 93) (codeMat 375) (codeMat 491) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane487GenSource0527 :
    QuotientRankAtLeast (spanCodes [257, 130, 67, 32, 16, 10, 7]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(257, 196), (130, 1), (67, 71), (32, 32), (16, 8), (10, 120), (7, 128)]
    (codeMat 85) (codeMat 331) (codeMat 410) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane487GenSource0528 :
    QuotientRankAtLeast (spanCodes [257, 128, 67, 34, 16, 10, 7]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(257, 112), (128, 216), (67, 248), (34, 198), (16, 3), (10, 199), (7, 128)]
    (codeMat 106) (codeMat 379) (codeMat 247) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane487GenSource0529 :
    QuotientRankAtLeast (spanCodes [259, 130, 67, 34, 16, 10, 7]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(259, 160), (130, 8), (67, 120), (34, 68), (16, 1), (10, 71), (7, 128)]
    (codeMat 106) (codeMat 331) (codeMat 410) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

end QiushiMatmul
