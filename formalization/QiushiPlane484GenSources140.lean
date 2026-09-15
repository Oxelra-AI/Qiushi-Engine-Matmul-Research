import QiushiPlane484GenData
import QiushiCertifiedTransport
import QiushiOrbit14FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane484GenSource1400 :
    QuotientRankAtLeast (spanCodes [257, 128, 67, 35, 19, 10, 7]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(257, 480), (128, 360), (67, 232), (35, 503), (19, 373), (10, 235), (7, 8)]
    (codeMat 335) (codeMat 431) (codeMat 477) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane484GenSource1401 :
    QuotientRankAtLeast (spanCodes [256, 130, 64, 35, 19, 10, 7]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 128), (130, 360), (64, 384), (35, 138), (19, 373), (10, 414), (7, 8)]
    (codeMat 271) (codeMat 234) (codeMat 461) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane484GenSource1402 :
    QuotientRankAtLeast (spanCodes [259, 129, 64, 35, 19, 10, 7]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(259, 139), (129, 245), (64, 360), (35, 138), (19, 373), (10, 235), (7, 130)]
    (codeMat 478) (codeMat 213) (codeMat 470) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane484GenSource1403 :
    QuotientRankAtLeast (spanCodes [256, 131, 65, 35, 19, 10, 7]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 9), (131, 245), (65, 360), (35, 138), (19, 373), (10, 235), (7, 130)]
    (codeMat 415) (codeMat 213) (codeMat 470) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane484GenSource1404 :
    QuotientRankAtLeast (spanCodes [259, 128, 65, 35, 19, 10, 7]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(259, 136), (128, 360), (65, 384), (35, 138), (19, 373), (10, 414), (7, 8)]
    (codeMat 334) (codeMat 234) (codeMat 461) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane484GenSource1405 :
    QuotientRankAtLeast (spanCodes [259, 128, 66, 32, 19, 10, 7]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(259, 139), (128, 360), (66, 245), (32, 8), (19, 235), (10, 373), (7, 130)]
    (codeMat 407) (codeMat 206) (codeMat 498) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane484GenSource1406 :
    QuotientRankAtLeast (spanCodes [258, 129, 66, 32, 19, 10, 7]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(258, 252), (129, 413), (66, 245), (32, 511), (19, 414), (10, 373), (7, 130)]
    (codeMat 415) (codeMat 382) (codeMat 499) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane484GenSource1407 :
    QuotientRankAtLeast (spanCodes [256, 130, 67, 32, 19, 10, 7]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 9), (130, 360), (67, 245), (32, 8), (19, 235), (10, 373), (7, 130)]
    (codeMat 470) (codeMat 206) (codeMat 498) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane484GenSource1408 :
    QuotientRankAtLeast (spanCodes [257, 131, 67, 32, 19, 10, 7]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(257, 126), (131, 413), (67, 245), (32, 511), (19, 414), (10, 373), (7, 130)]
    (codeMat 478) (codeMat 382) (codeMat 499) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane484GenSource1409 :
    QuotientRankAtLeast (spanCodes [259, 130, 64, 32, 19, 10, 7]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(259, 136), (130, 384), (64, 360), (32, 130), (19, 414), (10, 373), (7, 8)]
    (codeMat 335) (codeMat 241) (codeMat 489) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

end QiushiMatmul
