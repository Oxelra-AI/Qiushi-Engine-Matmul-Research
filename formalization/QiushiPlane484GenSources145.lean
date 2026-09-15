import QiushiPlane484GenData
import QiushiCertifiedTransport
import QiushiOrbit10FP
import QiushiOrbit14FP
import QiushiOrbit23FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane484GenSource1450 :
    QuotientRankAtLeast (spanCodes [256, 128, 66, 33, 19, 10, 5]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 128), (128, 384), (66, 246), (33, 381), (19, 235), (10, 414), (5, 511)]
    (codeMat 279) (codeMat 241) (codeMat 489) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane484GenSource1451 :
    QuotientRankAtLeast (spanCodes [259, 130, 67, 33, 19, 10, 5]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(259, 23), (130, 3), (67, 30), (33, 503), (19, 235), (10, 414), (5, 8)]
    (codeMat 461) (codeMat 382) (codeMat 499) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane484GenSource1452 :
    QuotientRankAtLeast (spanCodes [257, 128, 67, 33, 19, 10, 5]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(257, 510), (128, 360), (67, 363), (33, 503), (19, 414), (10, 235), (5, 511)]
    (codeMat 477) (codeMat 206) (codeMat 498) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane484GenSource1453 :
    QuotientRankAtLeast (spanCodes [257, 131, 64, 33, 19, 10, 5]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(257, 509), (131, 363), (64, 360), (33, 381), (19, 235), (10, 414), (5, 511)]
    (codeMat 405) (codeMat 241) (codeMat 489) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane484GenSource1454 :
    QuotientRankAtLeast (spanCodes [259, 129, 64, 33, 19, 10, 5]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(259, 126), (129, 413), (64, 360), (33, 381), (19, 414), (10, 235), (5, 130)]
    (codeMat 407) (codeMat 375) (codeMat 491) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane484GenSource1455 :
    QuotientRankAtLeast (spanCodes [256, 131, 65, 33, 19, 10, 5]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 9), (131, 246), (65, 384), (33, 503), (19, 414), (10, 235), (5, 511)]
    (codeMat 351) (codeMat 206) (codeMat 498) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane484GenSource1456 :
    QuotientRankAtLeast (spanCodes [258, 129, 65, 33, 19, 10, 5]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(258, 480), (129, 232), (65, 384), (33, 503), (19, 235), (10, 414), (5, 8)]
    (codeMat 335) (codeMat 382) (codeMat 499) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane484GenSource1457 :
    QuotientRankAtLeast (spanCodes [292, 129, 65, 17, 8, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 4, 8, 80, 128] [(292, 4), (129, 210), (65, 9), (17, 80), (8, 8), (2, 128)]
    (codeMat 87) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit23_lb12

theorem plane484GenSource1458 :
    QuotientRankAtLeast (spanCodes [256, 132, 68, 36, 17, 8, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(256, 1), (132, 68), (68, 70), (36, 8), (17, 160), (8, 432), (2, 256)]
    (codeMat 92) (codeMat 204) (codeMat 114) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane484GenSource1459 :
    QuotientRankAtLeast (spanCodes [256, 133, 69, 36, 17, 8, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(256, 3), (133, 324), (69, 326), (36, 24), (17, 160), (8, 432), (2, 256)]
    (codeMat 92) (codeMat 236) (codeMat 123) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

end QiushiMatmul
