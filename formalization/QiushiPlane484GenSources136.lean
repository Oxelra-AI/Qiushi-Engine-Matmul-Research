import QiushiPlane484GenData
import QiushiCertifiedTransport
import QiushiOrbit11FP
import QiushiOrbit14FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane484GenSource1360 :
    QuotientRankAtLeast (spanCodes [258, 194, 32, 18, 10, 4, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(258, 112), (194, 240), (32, 1), (18, 54), (10, 53), (4, 8), (1, 40)]
    (codeMat 266) (codeMat 213) (codeMat 470) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane484GenSource1361 :
    QuotientRankAtLeast (spanCodes [322, 128, 34, 18, 10, 4, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(322, 80), (128, 128), (34, 52), (18, 2), (10, 61), (4, 32), (1, 40)]
    (codeMat 267) (codeMat 337) (codeMat 337) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane484GenSource1362 :
    QuotientRankAtLeast (spanCodes [288, 128, 66, 18, 10, 6, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(288, 54), (128, 219), (66, 81), (18, 216), (10, 88), (6, 40), (1, 8)]
    (codeMat 143) (codeMat 307) (codeMat 311) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane484GenSource1363 :
    QuotientRankAtLeast (spanCodes [256, 194, 32, 18, 10, 6, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(256, 128), (194, 240), (32, 2), (18, 54), (10, 53), (6, 32), (1, 40)]
    (codeMat 266) (codeMat 241) (codeMat 489) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane484GenSource1364 :
    QuotientRankAtLeast (spanCodes [320, 130, 32, 18, 10, 6, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(320, 128), (130, 216), (32, 54), (18, 3), (10, 60), (6, 40), (1, 32)]
    (codeMat 267) (codeMat 370) (codeMat 207) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane484GenSource1365 :
    QuotientRankAtLeast (spanCodes [386, 64, 32, 18, 10, 6, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(386, 199), (64, 128), (32, 32), (18, 63), (10, 23), (6, 3), (1, 2)]
    (codeMat 273) (codeMat 410) (codeMat 331) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane484GenSource1366 :
    QuotientRankAtLeast (spanCodes [386, 66, 34, 18, 10, 6, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(386, 71), (66, 199), (34, 55), (18, 63), (10, 31), (6, 1), (1, 3)]
    (codeMat 273) (codeMat 443) (codeMat 254) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane484GenSource1367 :
    QuotientRankAtLeast (spanCodes [256, 128, 66, 34, 19, 10, 6]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 2), (128, 3), (66, 29), (34, 138), (19, 235), (10, 373), (6, 8)]
    (codeMat 460) (codeMat 115) (codeMat 492) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane484GenSource1368 :
    QuotientRankAtLeast (spanCodes [257, 129, 66, 34, 19, 10, 6]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(257, 23), (129, 30), (66, 29), (34, 503), (19, 414), (10, 373), (6, 8)]
    (codeMat 461) (codeMat 501) (codeMat 494) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane484GenSource1369 :
    QuotientRankAtLeast (spanCodes [259, 130, 67, 34, 19, 10, 6]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(259, 252), (130, 360), (67, 245), (34, 381), (19, 235), (10, 373), (6, 130)]
    (codeMat 470) (codeMat 494) (codeMat 501) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

end QiushiMatmul
