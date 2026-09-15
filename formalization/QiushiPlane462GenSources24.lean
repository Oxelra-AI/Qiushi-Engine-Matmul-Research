import QiushiPlane462GenData
import QiushiCertifiedTransport
import QiushiOrbit10FP
import QiushiOrbit11FP
import QiushiOrbit14FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane462GenSource0240 :
    QuotientRankAtLeast (spanCodes [273, 145, 64, 33, 8, 4, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(273, 116), (145, 118), (64, 1), (33, 96), (8, 8), (4, 256), (2, 384)]
    (codeMat 84) (codeMat 401) (codeMat 401) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane462GenSource0241 :
    QuotientRankAtLeast (spanCodes [272, 145, 65, 33, 8, 5, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(272, 373), (145, 502), (65, 1), (33, 104), (8, 8), (5, 256), (2, 384)]
    (codeMat 85) (codeMat 405) (codeMat 407) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane462GenSource0242 :
    QuotientRankAtLeast (spanCodes [256, 132, 68, 33, 20, 9, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 3), (132, 31), (68, 30), (33, 232), (20, 480), (9, 384), (3, 8)]
    (codeMat 204) (codeMat 254) (codeMat 443) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane462GenSource0243 :
    QuotientRankAtLeast (spanCodes [256, 132, 68, 32, 21, 9, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(256, 3), (132, 198), (68, 196), (32, 216), (21, 112), (9, 32), (3, 128)]
    (codeMat 92) (codeMat 244) (codeMat 95) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane462GenSource0244 :
    QuotientRankAtLeast (spanCodes [260, 128, 68, 33, 16, 9, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(260, 325), (128, 2), (68, 326), (33, 424), (16, 16), (9, 432), (3, 256)]
    (codeMat 84) (codeMat 348) (codeMat 125) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane462GenSource0245 :
    QuotientRankAtLeast (spanCodes [261, 129, 68, 33, 17, 9, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(261, 235), (129, 138), (68, 414), (33, 387), (17, 131), (9, 3), (3, 130)]
    (codeMat 171) (codeMat 271) (codeMat 314) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane462GenSource0246 :
    QuotientRankAtLeast (spanCodes [257, 129, 64, 48, 9, 4, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(257, 28), (129, 30), (64, 3), (48, 128), (9, 216), (4, 32), (3, 40)]
    (codeMat 140) (codeMat 409) (codeMat 473) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane462GenSource0247 :
    QuotientRankAtLeast (spanCodes [272, 144, 64, 33, 9, 4, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(272, 508), (144, 511), (64, 1), (33, 352), (9, 8), (4, 256), (3, 384)]
    (codeMat 92) (codeMat 403) (codeMat 403) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane462GenSource0248 :
    QuotientRankAtLeast (spanCodes [257, 131, 67, 32, 17, 10, 7]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(257, 97), (131, 276), (67, 406), (32, 360), (17, 148), (10, 150), (7, 511)]
    (codeMat 491) (codeMat 468) (codeMat 87) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane462GenSource0249 :
    QuotientRankAtLeast (spanCodes [256, 130, 67, 32, 16, 10, 7]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 8), (130, 130), (67, 406), (32, 1), (16, 2), (10, 150), (7, 511)]
    (codeMat 482) (codeMat 84) (codeMat 84) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

end QiushiMatmul
