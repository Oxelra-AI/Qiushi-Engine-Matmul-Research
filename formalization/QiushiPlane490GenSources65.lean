import QiushiPlane490GenData
import QiushiCertifiedTransport
import QiushiOrbit10FP
import QiushiOrbit11FP
import QiushiOrbit14FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane490GenSource0650 :
    QuotientRankAtLeast (spanCodes [260, 129, 64, 33, 20, 9, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(260, 384), (129, 104), (64, 8), (33, 510), (20, 148), (9, 1), (3, 360)]
    (codeMat 355) (codeMat 417) (codeMat 177) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane490GenSource0651 :
    QuotientRankAtLeast (spanCodes [260, 132, 68, 32, 20, 9, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(260, 1), (132, 257), (68, 385), (32, 8), (20, 105), (9, 511), (3, 130)]
    (codeMat 277) (codeMat 207) (codeMat 370) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane490GenSource0652 :
    QuotientRankAtLeast (spanCodes [256, 129, 64, 37, 16, 9, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(256, 54), (129, 91), (64, 9), (37, 112), (16, 216), (9, 8), (3, 128)]
    (codeMat 95) (codeMat 307) (codeMat 311) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane490GenSource0653 :
    QuotientRankAtLeast (spanCodes [256, 128, 68, 32, 16, 9, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(256, 1), (128, 2), (68, 70), (32, 8), (16, 16), (9, 432), (3, 256)]
    (codeMat 84) (codeMat 92) (codeMat 116) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane490GenSource0654 :
    QuotientRankAtLeast (spanCodes [256, 132, 64, 32, 16, 9, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 2), (132, 148), (64, 1), (32, 128), (16, 256), (9, 8), (3, 360)]
    (codeMat 156) (codeMat 161) (codeMat 161) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane490GenSource0655 :
    QuotientRankAtLeast (spanCodes [272, 144, 80, 49, 9, 5, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(272, 327), (144, 325), (80, 326), (49, 176), (9, 432), (5, 8), (3, 24)]
    (codeMat 140) (codeMat 494) (codeMat 501) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane490GenSource0656 :
    QuotientRankAtLeast (spanCodes [272, 129, 64, 48, 9, 5, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(272, 381), (129, 104), (64, 8), (48, 130), (9, 1), (5, 384), (3, 256)]
    (codeMat 99) (codeMat 423) (codeMat 181) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane490GenSource0657 :
    QuotientRankAtLeast (spanCodes [272, 128, 81, 32, 9, 5, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(272, 68), (128, 325), (81, 246), (32, 256), (9, 432), (5, 16), (3, 24)]
    (codeMat 142) (codeMat 458) (codeMat 458) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane490GenSource0658 :
    QuotientRankAtLeast (spanCodes [272, 144, 65, 33, 9, 4, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(272, 508), (144, 3), (65, 9), (33, 352), (9, 8), (4, 256), (3, 128)]
    (codeMat 94) (codeMat 275) (codeMat 275) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane490GenSource0659 :
    QuotientRankAtLeast (spanCodes [256, 193, 33, 16, 9, 4, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(256, 128), (193, 199), (33, 23), (16, 32), (9, 63), (4, 2), (3, 3)]
    (codeMat 273) (codeMat 233) (codeMat 233) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

end QiushiMatmul
