import QiushiPlane485GenData
import QiushiCertifiedTransport
import QiushiOrbit10FP
import QiushiOrbit14FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane485GenSource0350 :
    QuotientRankAtLeast (spanCodes [257, 129, 64, 35, 17, 10, 5]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(257, 352), (129, 224), (64, 256), (35, 381), (17, 227), (10, 284), (5, 8)]
    (codeMat 270) (codeMat 342) (codeMat 215) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane485GenSource0351 :
    QuotientRankAtLeast (spanCodes [259, 130, 65, 35, 17, 10, 5]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(259, 137), (130, 384), (65, 256), (35, 138), (17, 276), (10, 406), (5, 511)]
    (codeMat 342) (codeMat 244) (codeMat 95) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane485GenSource0352 :
    QuotientRankAtLeast (spanCodes [257, 128, 67, 33, 17, 10, 5]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(257, 259), (128, 325), (67, 327), (33, 280), (17, 168), (10, 184), (5, 256)]
    (codeMat 93) (codeMat 239) (codeMat 351) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane485GenSource0353 :
    QuotientRankAtLeast (spanCodes [257, 131, 64, 33, 17, 10, 5]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(257, 257), (131, 327), (64, 325), (33, 264), (17, 184), (10, 168), (5, 256)]
    (codeMat 93) (codeMat 215) (codeMat 342) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane485GenSource0354 :
    QuotientRankAtLeast (spanCodes [259, 129, 64, 33, 17, 10, 5]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(259, 406), (129, 227), (64, 511), (33, 392), (17, 224), (10, 480), (5, 8)]
    (codeMat 206) (codeMat 379) (codeMat 247) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane485GenSource0355 :
    QuotientRankAtLeast (spanCodes [261, 133, 64, 36, 20, 8, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(261, 326), (133, 324), (64, 3), (36, 432), (20, 416), (8, 24), (2, 256)]
    (codeMat 84) (codeMat 425) (codeMat 249) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane485GenSource0356 :
    QuotientRankAtLeast (spanCodes [257, 129, 64, 36, 20, 8, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(257, 70), (129, 68), (64, 1), (36, 432), (20, 416), (8, 8), (2, 256)]
    (codeMat 84) (codeMat 417) (codeMat 177) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane485GenSource0357 :
    QuotientRankAtLeast (spanCodes [260, 129, 65, 32, 20, 8, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(260, 2), (129, 324), (65, 1), (32, 16), (20, 160), (8, 8), (2, 256)]
    (codeMat 85) (codeMat 161) (codeMat 161) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane485GenSource0358 :
    QuotientRankAtLeast (spanCodes [256, 129, 96, 17, 8, 5, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(256, 325), (129, 162), (96, 68), (17, 160), (8, 256), (5, 8), (2, 16)]
    (codeMat 142) (codeMat 340) (codeMat 85) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane485GenSource0359 :
    QuotientRankAtLeast (spanCodes [257, 129, 97, 17, 8, 5, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(257, 487), (129, 162), (97, 228), (17, 160), (8, 256), (5, 24), (2, 16)]
    (codeMat 142) (codeMat 372) (codeMat 93) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

end QiushiMatmul
