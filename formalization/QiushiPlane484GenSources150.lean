import QiushiPlane484GenData
import QiushiCertifiedTransport
import QiushiOrbit14FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane484GenSource1500 :
    QuotientRankAtLeast (spanCodes [256, 128, 67, 35, 19, 10, 7]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 2), (128, 3), (67, 363), (35, 381), (19, 373), (10, 235), (7, 511)]
    (codeMat 468) (codeMat 122) (codeMat 460) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane484GenSource1501 :
    QuotientRankAtLeast (spanCodes [259, 130, 66, 35, 19, 10, 7]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(259, 509), (130, 3), (66, 363), (35, 381), (19, 373), (10, 235), (7, 511)]
    (codeMat 405) (codeMat 122) (codeMat 460) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane484GenSource1502 :
    QuotientRankAtLeast (spanCodes [256, 129, 66, 35, 19, 10, 7]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 9), (129, 374), (66, 246), (35, 503), (19, 373), (10, 414), (7, 511)]
    (codeMat 351) (codeMat 87) (codeMat 468) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane484GenSource1503 :
    QuotientRankAtLeast (spanCodes [259, 130, 67, 34, 19, 10, 7]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(259, 255), (130, 384), (67, 246), (34, 406), (19, 235), (10, 414), (7, 511)]
    (codeMat 342) (codeMat 465) (codeMat 465) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane484GenSource1504 :
    QuotientRankAtLeast (spanCodes [257, 128, 67, 34, 19, 10, 7]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(257, 150), (128, 360), (67, 363), (34, 105), (19, 414), (10, 235), (7, 511)]
    (codeMat 477) (codeMat 458) (codeMat 458) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane484GenSource1505 :
    QuotientRankAtLeast (spanCodes [258, 130, 66, 34, 19, 10, 7]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(258, 361), (130, 360), (66, 363), (34, 105), (19, 414), (10, 235), (7, 511)]
    (codeMat 412) (codeMat 458) (codeMat 458) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane484GenSource1506 :
    QuotientRankAtLeast (spanCodes [256, 128, 66, 34, 19, 10, 7]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 256), (128, 384), (66, 246), (34, 406), (19, 235), (10, 414), (7, 511)]
    (codeMat 279) (codeMat 465) (codeMat 465) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane484GenSource1507 :
    QuotientRankAtLeast (spanCodes [256, 131, 67, 32, 19, 10, 7]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 2), (131, 30), (67, 29), (32, 130), (19, 414), (10, 373), (7, 8)]
    (codeMat 396) (codeMat 241) (codeMat 489) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane484GenSource1508 :
    QuotientRankAtLeast (spanCodes [257, 130, 67, 32, 19, 10, 7]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(257, 23), (130, 3), (67, 29), (32, 511), (19, 235), (10, 373), (7, 8)]
    (codeMat 397) (codeMat 375) (codeMat 491) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane484GenSource1509 :
    QuotientRankAtLeast (spanCodes [259, 129, 66, 32, 19, 10, 7]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(259, 10), (129, 30), (66, 29), (32, 130), (19, 414), (10, 373), (7, 8)]
    (codeMat 461) (codeMat 241) (codeMat 489) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

end QiushiMatmul
