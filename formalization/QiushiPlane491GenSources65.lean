import QiushiPlane491GenData
import QiushiCertifiedTransport
import QiushiOrbit10FP
import QiushiOrbit11FP
import QiushiOrbit14FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane491GenSource0650 :
    QuotientRankAtLeast (spanCodes [258, 131, 67, 32, 16, 10, 7]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(258, 406), (131, 284), (67, 227), (32, 384), (16, 256), (10, 224), (7, 8)]
    (codeMat 143) (codeMat 425) (codeMat 249) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane491GenSource0651 :
    QuotientRankAtLeast (spanCodes [257, 128, 64, 35, 19, 9, 7]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(257, 100), (128, 63), (64, 9), (35, 160), (19, 120), (9, 8), (7, 128)]
    (codeMat 95) (codeMat 403) (codeMat 403) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane491GenSource0652 :
    QuotientRankAtLeast (spanCodes [256, 129, 64, 34, 19, 9, 7]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(256, 32), (129, 120), (64, 8), (34, 196), (19, 71), (9, 1), (7, 128)]
    (codeMat 99) (codeMat 403) (codeMat 403) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane491GenSource0653 :
    QuotientRankAtLeast (spanCodes [258, 130, 65, 33, 18, 9, 7]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(258, 327), (130, 2), (65, 1), (33, 440), (18, 16), (9, 8), (7, 256)]
    (codeMat 93) (codeMat 309) (codeMat 309) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane491GenSource0654 :
    QuotientRankAtLeast (spanCodes [257, 129, 64, 34, 19, 8, 7]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(257, 198), (129, 199), (64, 3), (34, 112), (19, 248), (8, 216), (7, 128)]
    (codeMat 92) (codeMat 443) (codeMat 254) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane491GenSource0655 :
    QuotientRankAtLeast (spanCodes [259, 129, 64, 34, 18, 10, 6]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(259, 373), (129, 227), (64, 511), (34, 258), (18, 256), (10, 259), (6, 130)]
    (codeMat 234) (codeMat 489) (codeMat 241) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane491GenSource0656 :
    QuotientRankAtLeast (spanCodes [258, 129, 66, 34, 16, 9, 6]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(258, 488), (129, 224), (66, 480), (34, 362), (16, 511), (9, 3), (6, 360)]
    (codeMat 355) (codeMat 187) (codeMat 229) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane491GenSource0657 :
    QuotientRankAtLeast (spanCodes [257, 130, 66, 33, 16, 9, 6]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(257, 71), (130, 3), (66, 326), (33, 440), (16, 24), (9, 432), (6, 256)]
    (codeMat 85) (codeMat 382) (codeMat 499) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane491GenSource0658 :
    QuotientRankAtLeast (spanCodes [258, 128, 65, 35, 16, 11, 5]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(258, 105), (128, 8), (65, 511), (35, 387), (16, 1), (11, 385), (5, 130)]
    (codeMat 226) (codeMat 335) (codeMat 426) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane491GenSource0659 :
    QuotientRankAtLeast (spanCodes [259, 128, 65, 35, 16, 10, 5]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(259, 374), (128, 9), (65, 256), (35, 373), (16, 8), (10, 105), (5, 511)]
    (codeMat 342) (codeMat 102) (codeMat 156) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

end QiushiMatmul
