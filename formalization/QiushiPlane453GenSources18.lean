import QiushiPlane453GenData
import QiushiCertifiedTransport
import QiushiOrbit11FP
import QiushiOrbit14FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane453GenSource0180 :
    QuotientRankAtLeast (spanCodes [260, 132, 68, 37, 20, 9, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(260, 3), (132, 387), (68, 259), (37, 284), (20, 235), (9, 511), (3, 130)]
    (codeMat 277) (codeMat 239) (codeMat 351) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane453GenSource0181 :
    QuotientRankAtLeast (spanCodes [260, 128, 68, 33, 20, 9, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(260, 511), (128, 3), (68, 510), (33, 392), (20, 480), (9, 384), (3, 360)]
    (codeMat 212) (codeMat 382) (codeMat 499) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane453GenSource0182 :
    QuotientRankAtLeast (spanCodes [257, 129, 66, 33, 18, 10, 6]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(257, 70), (129, 196), (66, 199), (33, 112), (18, 32), (10, 248), (6, 128)]
    (codeMat 93) (codeMat 489) (codeMat 241) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane453GenSource0183 :
    QuotientRankAtLeast (spanCodes [259, 130, 65, 35, 17, 10, 5]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(259, 137), (130, 384), (65, 256), (35, 138), (17, 276), (10, 406), (5, 511)]
    (codeMat 342) (codeMat 244) (codeMat 95) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane453GenSource0184 :
    QuotientRankAtLeast (spanCodes [257, 128, 65, 35, 17, 10, 5]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(257, 258), (128, 3), (65, 256), (35, 503), (17, 284), (10, 227), (5, 130)]
    (codeMat 340) (codeMat 370) (codeMat 207) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane453GenSource0185 :
    QuotientRankAtLeast (spanCodes [258, 130, 65, 34, 17, 10, 5]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(258, 240), (130, 40), (65, 32), (34, 198), (17, 69), (10, 68), (5, 128)]
    (codeMat 107) (codeMat 482) (codeMat 143) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane453GenSource0186 :
    QuotientRankAtLeast (spanCodes [256, 129, 64, 34, 16, 10, 4]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 1), (129, 28), (64, 3), (34, 96), (16, 256), (10, 224), (4, 8)]
    (codeMat 140) (codeMat 141) (codeMat 226) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane453GenSource0187 :
    QuotientRankAtLeast (spanCodes [260, 129, 68, 33, 20, 9, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(260, 54), (129, 191), (68, 237), (33, 240), (20, 120), (9, 40), (3, 128)]
    (codeMat 94) (codeMat 499) (codeMat 382) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane453GenSource0188 :
    QuotientRankAtLeast (spanCodes [260, 128, 68, 33, 20, 8, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(260, 256), (128, 2), (68, 259), (33, 227), (20, 406), (8, 511), (2, 130)]
    (codeMat 348) (codeMat 345) (codeMat 345) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane453GenSource0189 :
    QuotientRankAtLeast (spanCodes [256, 160, 65, 17, 8, 5, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 511), (160, 284), (65, 9), (17, 96), (8, 8), (5, 384), (2, 256)]
    (codeMat 87) (codeMat 421) (codeMat 179) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

end QiushiMatmul
