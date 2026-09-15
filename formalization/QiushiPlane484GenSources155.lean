import QiushiPlane484GenData
import QiushiCertifiedTransport
import QiushiOrbit14FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane484GenSource1550 :
    QuotientRankAtLeast (spanCodes [256, 130, 64, 32, 19, 10, 5]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 1), (130, 384), (64, 3), (32, 8), (19, 373), (10, 414), (5, 130)]
    (codeMat 340) (codeMat 157) (codeMat 486) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane484GenSource1551 :
    QuotientRankAtLeast (spanCodes [259, 128, 67, 35, 19, 10, 4]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(259, 104), (128, 384), (67, 232), (35, 97), (19, 414), (10, 235), (4, 8)]
    (codeMat 271) (codeMat 157) (codeMat 486) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane484GenSource1552 :
    QuotientRankAtLeast (spanCodes [256, 130, 66, 35, 19, 10, 4]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 128), (130, 3), (66, 387), (35, 406), (19, 414), (10, 235), (4, 130)]
    (codeMat 277) (codeMat 115) (codeMat 492) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane484GenSource1553 :
    QuotientRankAtLeast (spanCodes [258, 128, 66, 35, 19, 10, 4]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(258, 118), (128, 384), (66, 246), (35, 227), (19, 235), (10, 414), (4, 511)]
    (codeMat 279) (codeMat 501) (codeMat 494) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane484GenSource1554 :
    QuotientRankAtLeast (spanCodes [256, 129, 65, 35, 19, 10, 4]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 128), (129, 387), (65, 3), (35, 276), (19, 235), (10, 414), (4, 130)]
    (codeMat 285) (codeMat 171) (codeMat 485) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane484GenSource1555 :
    QuotientRankAtLeast (spanCodes [259, 131, 64, 35, 19, 10, 4]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(259, 104), (131, 232), (64, 384), (35, 105), (19, 235), (10, 414), (4, 8)]
    (codeMat 270) (codeMat 94) (codeMat 500) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane484GenSource1556 :
    QuotientRankAtLeast (spanCodes [257, 129, 64, 35, 19, 10, 4]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(257, 118), (129, 246), (64, 384), (35, 284), (19, 414), (10, 235), (4, 511)]
    (codeMat 286) (codeMat 494) (codeMat 501) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane484GenSource1557 :
    QuotientRankAtLeast (spanCodes [258, 128, 67, 34, 19, 10, 4]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(258, 96), (128, 360), (67, 232), (34, 105), (19, 373), (10, 235), (4, 8)]
    (codeMat 335) (codeMat 143) (codeMat 482) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane484GenSource1558 :
    QuotientRankAtLeast (spanCodes [258, 129, 66, 34, 19, 10, 4]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(258, 404), (129, 245), (66, 413), (34, 406), (19, 373), (10, 414), (4, 130)]
    (codeMat 470) (codeMat 185) (codeMat 481) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane484GenSource1559 :
    QuotientRankAtLeast (spanCodes [256, 128, 65, 34, 19, 10, 4]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 128), (128, 384), (65, 3), (34, 406), (19, 373), (10, 414), (4, 130)]
    (codeMat 277) (codeMat 185) (codeMat 481) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

end QiushiMatmul
