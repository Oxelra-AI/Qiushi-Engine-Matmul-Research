import QiushiPlane452GenData
import QiushiCertifiedTransport
import QiushiFlattenSeeds
import QiushiOrbit14FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane452GenSource0110 :
    QuotientRankAtLeast (spanCodes [260, 132, 65, 33, 20, 8, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(260, 256), (132, 104), (65, 128), (33, 276), (20, 97), (8, 130), (2, 8)]
    (codeMat 335) (codeMat 266) (codeMat 266) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane452GenSource0111 :
    QuotientRankAtLeast (spanCodes [256, 129, 65, 35, 16, 10, 4]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 128), (129, 259), (65, 3), (35, 406), (16, 511), (10, 284), (4, 130)]
    (codeMat 285) (codeMat 187) (codeMat 229) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane452GenSource0112 :
    QuotientRankAtLeast (spanCodes [259, 129, 67, 35, 16, 10, 4]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(259, 278), (129, 252), (67, 287), (35, 406), (16, 511), (10, 284), (4, 130)]
    (codeMat 415) (codeMat 187) (codeMat 229) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane452GenSource0113 :
    QuotientRankAtLeast (spanCodes [258, 131, 65, 35, 19, 10, 7]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(258, 23), (131, 29), (65, 3), (35, 503), (19, 373), (10, 235), (7, 8)]
    (codeMat 461) (codeMat 431) (codeMat 477) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane452GenSource0114 :
    QuotientRankAtLeast (spanCodes [256, 133, 65, 32, 20, 9, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 9), (133, 246), (65, 128), (32, 8), (20, 97), (9, 130), (3, 511)]
    (codeMat 342) (codeMat 142) (codeMat 354) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane452GenSource0115 :
    QuotientRankAtLeast (spanCodes [260, 128, 68, 32, 20, 8, 2, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(260, 325), (128, 2), (68, 324), (32, 40), (20, 336), (8, 32), (2, 128), (1, 256)]
    (codeMat 84) (codeMat 340) (codeMat 85) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

theorem plane452GenSource0116 :
    QuotientRankAtLeast (spanCodes [256, 128, 68, 32, 20, 8, 2, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(256, 1), (128, 2), (68, 68), (32, 8), (20, 80), (8, 32), (2, 128), (1, 256)]
    (codeMat 84) (codeMat 84) (codeMat 84) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

end QiushiMatmul
