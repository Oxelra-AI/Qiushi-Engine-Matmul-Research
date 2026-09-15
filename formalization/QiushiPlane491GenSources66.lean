import QiushiPlane491GenData
import QiushiCertifiedTransport
import QiushiOrbit10FP
import QiushiOrbit11FP
import QiushiOrbit14FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane491GenSource0660 :
    QuotientRankAtLeast (spanCodes [256, 130, 66, 33, 19, 8, 5]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(256, 2), (130, 325), (66, 326), (33, 272), (19, 424), (8, 432), (5, 256)]
    (codeMat 92) (codeMat 234) (codeMat 461) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane491GenSource0661 :
    QuotientRankAtLeast (spanCodes [257, 130, 67, 33, 18, 8, 5]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(257, 258), (130, 1), (67, 70), (33, 272), (18, 8), (8, 432), (5, 256)]
    (codeMat 93) (codeMat 106) (codeMat 396) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane491GenSource0662 :
    QuotientRankAtLeast (spanCodes [258, 130, 64, 33, 17, 8, 5]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(258, 326), (130, 325), (64, 2), (33, 176), (17, 168), (8, 16), (5, 256)]
    (codeMat 84) (codeMat 426) (codeMat 335) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane491GenSource0663 :
    QuotientRankAtLeast (spanCodes [259, 131, 64, 32, 17, 8, 5]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(259, 232), (131, 488), (64, 128), (32, 3), (17, 23), (8, 2), (5, 8)]
    (codeMat 266) (codeMat 190) (codeMat 355) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane491GenSource0664 :
    QuotientRankAtLeast (spanCodes [259, 130, 65, 33, 16, 8, 5]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(259, 326), (130, 1), (65, 2), (33, 176), (16, 8), (8, 16), (5, 256)]
    (codeMat 85) (codeMat 298) (codeMat 270) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane491GenSource0665 :
    QuotientRankAtLeast (spanCodes [259, 131, 67, 32, 19, 11, 4]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(259, 80), (131, 112), (67, 120), (32, 2), (19, 70), (11, 71), (4, 128)]
    (codeMat 98) (codeMat 249) (codeMat 425) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane491GenSource0666 :
    QuotientRankAtLeast (spanCodes [257, 130, 65, 33, 17, 10, 4]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(257, 104), (130, 384), (65, 256), (33, 105), (17, 406), (10, 276), (4, 8)]
    (codeMat 334) (codeMat 212) (codeMat 86) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane491GenSource0667 :
    QuotientRankAtLeast (spanCodes [257, 131, 64, 32, 16, 10, 4]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(257, 96), (131, 232), (64, 360), (32, 1), (16, 3), (10, 29), (4, 8)]
    (codeMat 330) (codeMat 87) (codeMat 468) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane491GenSource0668 :
    QuotientRankAtLeast (spanCodes [258, 129, 66, 34, 18, 9, 4]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(258, 105), (129, 276), (66, 406), (34, 104), (18, 256), (9, 384), (4, 8)]
    (codeMat 206) (codeMat 204) (codeMat 114) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane491GenSource0669 :
    QuotientRankAtLeast (spanCodes [259, 128, 67, 35, 19, 8, 4]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(259, 210), (128, 54), (67, 237), (35, 208), (19, 240), (8, 40), (4, 128)]
    (codeMat 86) (codeMat 241) (codeMat 489) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

end QiushiMatmul
