import QiushiPlane484GenData
import QiushiCertifiedTransport
import QiushiOrbit14FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane484GenSource1280 :
    QuotientRankAtLeast (spanCodes [258, 130, 64, 35, 19, 10, 7]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(258, 385), (130, 384), (64, 3), (35, 381), (19, 373), (10, 414), (7, 130)]
    (codeMat 340) (codeMat 445) (codeMat 478) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane484GenSource1281 :
    QuotientRankAtLeast (spanCodes [257, 128, 65, 35, 19, 10, 7]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(257, 259), (128, 384), (65, 3), (35, 381), (19, 373), (10, 414), (7, 130)]
    (codeMat 277) (codeMat 445) (codeMat 478) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane484GenSource1282 :
    QuotientRankAtLeast (spanCodes [258, 131, 65, 35, 19, 10, 7]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(258, 23), (131, 29), (65, 3), (35, 503), (19, 373), (10, 235), (7, 8)]
    (codeMat 461) (codeMat 431) (codeMat 477) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane484GenSource1283 :
    QuotientRankAtLeast (spanCodes [259, 129, 66, 35, 19, 10, 7]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(259, 10), (129, 29), (66, 30), (35, 138), (19, 373), (10, 414), (7, 8)]
    (codeMat 397) (codeMat 234) (codeMat 461) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane484GenSource1284 :
    QuotientRankAtLeast (spanCodes [256, 130, 66, 35, 19, 10, 7]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 1), (130, 384), (66, 387), (35, 138), (19, 373), (10, 235), (7, 130)]
    (codeMat 348) (codeMat 213) (codeMat 470) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane484GenSource1285 :
    QuotientRankAtLeast (spanCodes [259, 128, 67, 35, 19, 10, 7]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(259, 131), (128, 384), (67, 387), (35, 138), (19, 373), (10, 235), (7, 130)]
    (codeMat 285) (codeMat 213) (codeMat 470) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane484GenSource1286 :
    QuotientRankAtLeast (spanCodes [256, 131, 67, 35, 19, 10, 7]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 2), (131, 29), (67, 30), (35, 138), (19, 373), (10, 414), (7, 8)]
    (codeMat 460) (codeMat 234) (codeMat 461) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane484GenSource1287 :
    QuotientRankAtLeast (spanCodes [257, 129, 65, 33, 19, 10, 5]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(257, 131), (129, 387), (65, 3), (33, 138), (19, 235), (10, 414), (5, 130)]
    (codeMat 285) (codeMat 143) (codeMat 482) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane484GenSource1288 :
    QuotientRankAtLeast (spanCodes [256, 129, 64, 33, 19, 10, 5]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 2), (129, 30), (64, 3), (33, 138), (19, 414), (10, 235), (5, 8)]
    (codeMat 460) (codeMat 185) (codeMat 481) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane484GenSource1289 :
    QuotientRankAtLeast (spanCodes [256, 130, 67, 33, 19, 10, 5]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 9), (130, 360), (67, 413), (33, 138), (19, 235), (10, 414), (5, 130)]
    (codeMat 415) (codeMat 143) (codeMat 482) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

end QiushiMatmul
