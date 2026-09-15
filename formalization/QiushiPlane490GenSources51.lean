import QiushiPlane490GenData
import QiushiCertifiedTransport
import QiushiOrbit10FP
import QiushiOrbit11FP
import QiushiOrbit14FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane490GenSource0510 :
    QuotientRankAtLeast (spanCodes [261, 133, 69, 37, 21, 9, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(261, 28), (133, 30), (69, 31), (37, 284), (21, 414), (9, 511), (3, 8)]
    (codeMat 396) (codeMat 473) (codeMat 409) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane490GenSource0511 :
    QuotientRankAtLeast (spanCodes [260, 129, 68, 33, 20, 9, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(260, 54), (129, 191), (68, 237), (33, 240), (20, 120), (9, 40), (3, 128)]
    (codeMat 94) (codeMat 499) (codeMat 382) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane490GenSource0512 :
    QuotientRankAtLeast (spanCodes [260, 132, 64, 32, 20, 9, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(260, 9), (132, 265), (64, 128), (32, 8), (20, 97), (9, 130), (3, 511)]
    (codeMat 279) (codeMat 142) (codeMat 354) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane490GenSource0513 :
    QuotientRankAtLeast (spanCodes [256, 129, 64, 33, 17, 8, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(256, 54), (129, 82), (64, 9), (33, 112), (17, 80), (8, 8), (2, 128)]
    (codeMat 86) (codeMat 305) (codeMat 305) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane490GenSource0514 :
    QuotientRankAtLeast (spanCodes [256, 132, 64, 36, 17, 8, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 2), (132, 149), (64, 1), (36, 128), (17, 96), (8, 8), (2, 360)]
    (codeMat 212) (codeMat 163) (codeMat 165) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane490GenSource0515 :
    QuotientRankAtLeast (spanCodes [256, 128, 68, 36, 17, 8, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 2), (128, 1), (68, 21), (36, 128), (17, 96), (8, 360), (2, 8)]
    (codeMat 204) (codeMat 99) (codeMat 172) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane490GenSource0516 :
    QuotientRankAtLeast (spanCodes [257, 129, 65, 33, 16, 8, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(257, 240), (129, 208), (65, 216), (33, 198), (16, 2), (8, 3), (2, 128)]
    (codeMat 98) (codeMat 313) (codeMat 313) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane490GenSource0517 :
    QuotientRankAtLeast (spanCodes [260, 133, 68, 37, 21, 8, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(260, 54), (133, 82), (68, 237), (37, 240), (21, 208), (8, 40), (2, 128)]
    (codeMat 87) (codeMat 369) (codeMat 377) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane490GenSource0518 :
    QuotientRankAtLeast (spanCodes [256, 134, 68, 34, 18, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(256, 325), (134, 326), (68, 68), (34, 424), (18, 432), (10, 416), (1, 256)]
    (codeMat 85) (codeMat 468) (codeMat 87) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane490GenSource0519 :
    QuotientRankAtLeast (spanCodes [256, 134, 70, 32, 18, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(256, 3), (134, 326), (70, 324), (32, 24), (18, 432), (10, 416), (1, 256)]
    (codeMat 84) (codeMat 244) (codeMat 95) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

end QiushiMatmul
