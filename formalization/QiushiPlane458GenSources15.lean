import QiushiPlane458GenData
import QiushiCertifiedTransport
import QiushiOrbit11FP
import QiushiOrbit14FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane458GenSource0150 :
    QuotientRankAtLeast (spanCodes [256, 129, 64, 33, 20, 9, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 3), (129, 151), (64, 2), (33, 136), (20, 224), (9, 128), (3, 360)]
    (codeMat 212) (codeMat 190) (codeMat 355) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane458GenSource0151 :
    QuotientRankAtLeast (spanCodes [256, 132, 68, 33, 20, 8, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 256), (132, 96), (68, 480), (33, 284), (20, 105), (8, 511), (2, 8)]
    (codeMat 271) (codeMat 331) (codeMat 410) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane458GenSource0152 :
    QuotientRankAtLeast (spanCodes [260, 130, 68, 36, 20, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(260, 2), (130, 3), (68, 362), (36, 130), (20, 138), (10, 227), (1, 511)]
    (codeMat 405) (codeMat 123) (codeMat 236) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane458GenSource0153 :
    QuotientRankAtLeast (spanCodes [258, 128, 64, 32, 16, 10, 4]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(258, 80), (128, 8), (64, 32), (32, 2), (16, 1), (10, 68), (4, 128)]
    (codeMat 98) (codeMat 98) (codeMat 140) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane458GenSource0154 :
    QuotientRankAtLeast (spanCodes [258, 130, 66, 32, 16, 10, 4]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(258, 208), (130, 216), (66, 240), (32, 2), (16, 3), (10, 198), (4, 128)]
    (codeMat 98) (codeMat 122) (codeMat 460) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane458GenSource0155 :
    QuotientRankAtLeast (spanCodes [256, 128, 66, 34, 16, 10, 4]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(256, 2), (128, 1), (66, 70), (34, 80), (16, 8), (10, 112), (4, 128)]
    (codeMat 84) (codeMat 106) (codeMat 396) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane458GenSource0156 :
    QuotientRankAtLeast (spanCodes [258, 131, 67, 33, 17, 10, 5]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(258, 373), (131, 276), (67, 406), (33, 508), (17, 148), (10, 150), (5, 511)]
    (codeMat 491) (codeMat 244) (codeMat 95) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane458GenSource0157 :
    QuotientRankAtLeast (spanCodes [257, 129, 66, 34, 17, 10, 5]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(257, 160), (129, 120), (66, 112), (34, 196), (17, 71), (10, 70), (5, 128)]
    (codeMat 107) (codeMat 474) (codeMat 395) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane458GenSource0158 :
    QuotientRankAtLeast (spanCodes [256, 131, 65, 35, 17, 10, 5]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 360), (131, 224), (65, 256), (35, 381), (17, 227), (10, 284), (5, 8)]
    (codeMat 335) (codeMat 342) (codeMat 215) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane458GenSource0159 :
    QuotientRankAtLeast (spanCodes [256, 130, 64, 32, 18, 10, 6]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(256, 9), (130, 219), (64, 54), (32, 8), (18, 216), (10, 240), (6, 128)]
    (codeMat 86) (codeMat 94) (codeMat 500) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

end QiushiMatmul
