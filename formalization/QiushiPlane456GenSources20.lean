import QiushiPlane456GenData
import QiushiCertifiedTransport
import QiushiOrbit10FP
import QiushiOrbit14FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane456GenSource0200 :
    QuotientRankAtLeast (spanCodes [258, 129, 66, 32, 18, 10, 6]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(258, 258), (129, 70), (66, 71), (32, 16), (18, 432), (10, 440), (6, 256)]
    (codeMat 85) (codeMat 249) (codeMat 425) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane456GenSource0201 :
    QuotientRankAtLeast (spanCodes [258, 131, 65, 34, 19, 10, 7]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(258, 20), (131, 30), (65, 3), (34, 276), (19, 414), (10, 235), (7, 8)]
    (codeMat 397) (codeMat 409) (codeMat 473) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane456GenSource0202 :
    QuotientRankAtLeast (spanCodes [256, 130, 66, 35, 19, 10, 7]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 1), (130, 384), (66, 387), (35, 138), (19, 373), (10, 235), (7, 130)]
    (codeMat 348) (codeMat 213) (codeMat 470) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane456GenSource0203 :
    QuotientRankAtLeast (spanCodes [257, 130, 64, 35, 16, 10, 4]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(257, 149), (130, 1), (64, 360), (35, 284), (16, 8), (10, 97), (4, 511)]
    (codeMat 405) (codeMat 359) (codeMat 174) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane456GenSource0204 :
    QuotientRankAtLeast (spanCodes [259, 129, 65, 32, 16, 10, 4]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(259, 96), (129, 232), (65, 384), (32, 1), (16, 3), (10, 30), (4, 8)]
    (codeMat 330) (codeMat 94) (codeMat 500) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane456GenSource0205 :
    QuotientRankAtLeast (spanCodes [259, 128, 64, 33, 16, 10, 4]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(259, 118), (128, 128), (64, 256), (33, 227), (16, 130), (10, 406), (4, 511)]
    (codeMat 286) (codeMat 372) (codeMat 93) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane456GenSource0206 :
    QuotientRankAtLeast (spanCodes [258, 128, 65, 33, 16, 10, 4]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(258, 118), (128, 9), (65, 256), (33, 284), (16, 8), (10, 105), (4, 511)]
    (codeMat 342) (codeMat 358) (codeMat 158) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane456GenSource0207 :
    QuotientRankAtLeast (spanCodes [257, 128, 67, 33, 17, 10, 5]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(257, 259), (128, 325), (67, 327), (33, 280), (17, 168), (10, 184), (5, 256)]
    (codeMat 93) (codeMat 239) (codeMat 351) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane456GenSource0208 :
    QuotientRankAtLeast (spanCodes [257, 133, 65, 36, 20, 8, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(257, 326), (133, 68), (65, 3), (36, 432), (20, 416), (8, 24), (2, 256)]
    (codeMat 85) (codeMat 425) (codeMat 249) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane456GenSource0209 :
    QuotientRankAtLeast (spanCodes [260, 129, 64, 32, 20, 8, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(260, 128), (129, 96), (64, 8), (32, 2), (20, 149), (8, 1), (2, 360)]
    (codeMat 354) (codeMat 163) (codeMat 165) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

end QiushiMatmul
