import QiushiPlane454GenData
import QiushiCertifiedTransport
import QiushiOrbit10FP
import QiushiOrbit11FP
import QiushiOrbit14FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane454GenSource0130 :
    QuotientRankAtLeast (spanCodes [260, 134, 64, 32, 20, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(260, 2), (134, 20), (64, 9), (32, 130), (20, 276), (10, 97), (1, 8)]
    (codeMat 461) (codeMat 161) (codeMat 161) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane454GenSource0131 :
    QuotientRankAtLeast (spanCodes [257, 131, 66, 34, 16, 10, 4]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(257, 413), (131, 252), (66, 483), (34, 96), (16, 256), (10, 480), (4, 360)]
    (codeMat 158) (codeMat 397) (codeMat 250) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane454GenSource0132 :
    QuotientRankAtLeast (spanCodes [258, 130, 65, 33, 17, 10, 5]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(258, 228), (130, 63), (65, 54), (33, 160), (17, 120), (10, 112), (5, 128)]
    (codeMat 94) (codeMat 474) (codeMat 395) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane454GenSource0133 :
    QuotientRankAtLeast (spanCodes [257, 130, 66, 34, 17, 10, 5]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(257, 160), (130, 40), (66, 240), (34, 68), (17, 197), (10, 198), (5, 128)]
    (codeMat 107) (codeMat 458) (codeMat 458) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane454GenSource0134 :
    QuotientRankAtLeast (spanCodes [258, 129, 65, 33, 18, 10, 6]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(258, 182), (129, 228), (65, 63), (33, 112), (18, 32), (10, 248), (6, 128)]
    (codeMat 94) (codeMat 489) (codeMat 241) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane454GenSource0135 :
    QuotientRankAtLeast (spanCodes [256, 129, 65, 33, 17, 10, 5]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(256, 1), (129, 327), (65, 325), (33, 264), (17, 184), (10, 168), (5, 256)]
    (codeMat 92) (codeMat 215) (codeMat 342) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane454GenSource0136 :
    QuotientRankAtLeast (spanCodes [256, 131, 67, 35, 17, 10, 5]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 3), (131, 148), (67, 150), (35, 138), (17, 276), (10, 406), (5, 511)]
    (codeMat 468) (codeMat 244) (codeMat 95) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane454GenSource0137 :
    QuotientRankAtLeast (spanCodes [259, 130, 64, 32, 16, 10, 4]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(259, 97), (130, 130), (64, 511), (32, 1), (16, 2), (10, 23), (4, 8)]
    (codeMat 458) (codeMat 93) (codeMat 372) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane454GenSource0138 :
    QuotientRankAtLeast (spanCodes [259, 129, 67, 35, 16, 10, 4]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(259, 278), (129, 252), (67, 287), (35, 406), (16, 511), (10, 284), (4, 130)]
    (codeMat 415) (codeMat 187) (codeMat 229) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane454GenSource0139 :
    QuotientRankAtLeast (spanCodes [257, 128, 67, 35, 19, 10, 7]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(257, 480), (128, 360), (67, 232), (35, 503), (19, 373), (10, 235), (7, 8)]
    (codeMat 335) (codeMat 431) (codeMat 477) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

end QiushiMatmul
