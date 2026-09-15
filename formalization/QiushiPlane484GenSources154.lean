import QiushiPlane484GenData
import QiushiCertifiedTransport
import QiushiOrbit14FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane484GenSource1540 :
    QuotientRankAtLeast (spanCodes [256, 128, 65, 35, 19, 10, 5]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 256), (128, 384), (65, 360), (35, 284), (19, 414), (10, 373), (5, 8)]
    (codeMat 270) (codeMat 465) (codeMat 465) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane484GenSource1541 :
    QuotientRankAtLeast (spanCodes [256, 128, 67, 33, 19, 10, 5]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 128), (128, 384), (67, 232), (33, 138), (19, 414), (10, 235), (5, 8)]
    (codeMat 271) (codeMat 185) (codeMat 481) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane484GenSource1542 :
    QuotientRankAtLeast (spanCodes [257, 128, 66, 33, 19, 10, 5]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(257, 139), (128, 360), (66, 413), (33, 138), (19, 235), (10, 414), (5, 130)]
    (codeMat 478) (codeMat 143) (codeMat 482) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane484GenSource1543 :
    QuotientRankAtLeast (spanCodes [257, 131, 65, 33, 19, 10, 5]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(257, 10), (131, 30), (65, 3), (33, 138), (19, 414), (10, 235), (5, 8)]
    (codeMat 397) (codeMat 185) (codeMat 481) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane484GenSource1544 :
    QuotientRankAtLeast (spanCodes [256, 131, 64, 33, 19, 10, 5]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 1), (131, 387), (64, 3), (33, 138), (19, 235), (10, 414), (5, 130)]
    (codeMat 348) (codeMat 143) (codeMat 482) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane484GenSource1545 :
    QuotientRankAtLeast (spanCodes [257, 128, 67, 32, 19, 10, 5]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(257, 136), (128, 360), (67, 232), (32, 130), (19, 373), (10, 235), (5, 8)]
    (codeMat 335) (codeMat 171) (codeMat 485) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane484GenSource1546 :
    QuotientRankAtLeast (spanCodes [258, 130, 66, 32, 19, 10, 5]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(258, 385), (130, 384), (66, 387), (32, 511), (19, 373), (10, 235), (5, 130)]
    (codeMat 348) (codeMat 501) (codeMat 494) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane484GenSource1547 :
    QuotientRankAtLeast (spanCodes [257, 129, 66, 32, 19, 10, 5]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(257, 383), (129, 374), (66, 246), (32, 130), (19, 373), (10, 414), (5, 511)]
    (codeMat 351) (codeMat 115) (codeMat 492) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane484GenSource1548 :
    QuotientRankAtLeast (spanCodes [256, 131, 65, 32, 19, 10, 5]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 9), (131, 374), (65, 384), (32, 8), (19, 373), (10, 235), (5, 511)]
    (codeMat 342) (codeMat 94) (codeMat 500) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane484GenSource1549 :
    QuotientRankAtLeast (spanCodes [259, 128, 65, 32, 19, 10, 5]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(259, 480), (128, 360), (65, 384), (32, 511), (19, 373), (10, 414), (5, 8)]
    (codeMat 334) (codeMat 494) (codeMat 501) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

end QiushiMatmul
