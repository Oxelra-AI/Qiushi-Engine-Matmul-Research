import QiushiPlane490GenData
import QiushiCertifiedTransport
import QiushiOrbit10FP
import QiushiOrbit14FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane490GenSource0620 :
    QuotientRankAtLeast (spanCodes [256, 129, 65, 34, 19, 10, 6]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 128), (129, 232), (65, 360), (34, 138), (19, 235), (10, 373), (6, 8)]
    (codeMat 271) (codeMat 115) (codeMat 492) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane490GenSource0621 :
    QuotientRankAtLeast (spanCodes [256, 128, 66, 32, 19, 10, 6]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 2), (128, 3), (66, 30), (32, 130), (19, 235), (10, 414), (6, 8)]
    (codeMat 396) (codeMat 122) (codeMat 460) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane490GenSource0622 :
    QuotientRankAtLeast (spanCodes [256, 131, 65, 32, 19, 10, 6]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 9), (131, 413), (65, 360), (32, 8), (19, 414), (10, 235), (6, 130)]
    (codeMat 470) (codeMat 87) (codeMat 468) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane490GenSource0623 :
    QuotientRankAtLeast (spanCodes [257, 129, 65, 35, 18, 10, 6]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(257, 387), (129, 385), (65, 384), (35, 105), (18, 511), (10, 503), (6, 130)]
    (codeMat 340) (codeMat 478) (codeMat 445) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane490GenSource0624 :
    QuotientRankAtLeast (spanCodes [257, 130, 65, 32, 18, 10, 6]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(257, 508), (130, 1), (65, 3), (32, 256), (18, 8), (10, 136), (6, 360)]
    (codeMat 157) (codeMat 267) (codeMat 282) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane490GenSource0625 :
    QuotientRankAtLeast (spanCodes [259, 128, 67, 34, 16, 10, 6]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(259, 326), (128, 2), (67, 327), (34, 176), (16, 16), (10, 184), (6, 256)]
    (codeMat 84) (codeMat 377) (codeMat 369) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane490GenSource0626 :
    QuotientRankAtLeast (spanCodes [256, 128, 66, 35, 19, 10, 5]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 256), (128, 384), (66, 374), (35, 105), (19, 235), (10, 373), (5, 511)]
    (codeMat 286) (codeMat 409) (codeMat 473) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane490GenSource0627 :
    QuotientRankAtLeast (spanCodes [256, 130, 64, 35, 19, 10, 5]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 256), (130, 3), (64, 384), (35, 97), (19, 414), (10, 373), (5, 130)]
    (codeMat 285) (codeMat 346) (codeMat 459) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane490GenSource0628 :
    QuotientRankAtLeast (spanCodes [256, 128, 65, 32, 19, 10, 5]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 2), (128, 3), (65, 360), (32, 130), (19, 373), (10, 414), (5, 511)]
    (codeMat 412) (codeMat 115) (codeMat 492) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane490GenSource0629 :
    QuotientRankAtLeast (spanCodes [256, 129, 64, 32, 19, 10, 5]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 2), (129, 29), (64, 3), (32, 130), (19, 373), (10, 235), (5, 8)]
    (codeMat 396) (codeMat 171) (codeMat 485) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

end QiushiMatmul
