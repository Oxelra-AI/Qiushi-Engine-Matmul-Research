import QiushiPlane487GenData
import QiushiCertifiedTransport
import QiushiOrbit10FP
import QiushiOrbit11FP
import QiushiOrbit14FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane487GenSource0610 :
    QuotientRankAtLeast (spanCodes [289, 128, 65, 16, 9, 5, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(289, 30), (128, 130), (65, 219), (16, 128), (9, 216), (5, 40), (3, 8)]
    (codeMat 142) (codeMat 313) (codeMat 313) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane487GenSource0611 :
    QuotientRankAtLeast (spanCodes [385, 65, 32, 16, 9, 5, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(385, 88), (65, 216), (32, 54), (16, 63), (9, 3), (5, 40), (3, 32)]
    (codeMat 267) (codeMat 443) (codeMat 254) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane487GenSource0612 :
    QuotientRankAtLeast (spanCodes [272, 129, 80, 33, 9, 4, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(272, 28), (129, 383), (80, 21), (33, 352), (9, 360), (4, 256), (3, 128)]
    (codeMat 86) (codeMat 467) (codeMat 339) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane487GenSource0613 :
    QuotientRankAtLeast (spanCodes [256, 160, 64, 16, 9, 4, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 2), (160, 149), (64, 1), (16, 360), (9, 8), (4, 128), (3, 256)]
    (codeMat 92) (codeMat 163) (codeMat 165) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane487GenSource0614 :
    QuotientRankAtLeast (spanCodes [289, 129, 64, 16, 9, 4, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(289, 60), (129, 138), (64, 219), (16, 128), (9, 216), (4, 32), (3, 8)]
    (codeMat 143) (codeMat 281) (codeMat 281) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane487GenSource0615 :
    QuotientRankAtLeast (spanCodes [385, 64, 33, 16, 9, 4, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(385, 208), (64, 128), (33, 52), (16, 63), (9, 2), (4, 32), (3, 40)]
    (codeMat 267) (codeMat 410) (codeMat 331) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane487GenSource0616 :
    QuotientRankAtLeast (spanCodes [257, 132, 65, 37, 21, 8, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(257, 139), (132, 245), (65, 130), (37, 136), (21, 264), (8, 128), (2, 360)]
    (codeMat 159) (codeMat 174) (codeMat 359) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane487GenSource0617 :
    QuotientRankAtLeast (spanCodes [260, 129, 65, 37, 21, 8, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(260, 3), (129, 509), (65, 2), (37, 136), (21, 264), (8, 128), (2, 360)]
    (codeMat 157) (codeMat 174) (codeMat 359) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane487GenSource0618 :
    QuotientRankAtLeast (spanCodes [260, 132, 65, 32, 21, 8, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(260, 1), (132, 324), (65, 3), (32, 8), (21, 160), (8, 24), (2, 256)]
    (codeMat 85) (codeMat 141) (codeMat 226) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane487GenSource0619 :
    QuotientRankAtLeast (spanCodes [256, 129, 64, 32, 20, 8, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(256, 2), (129, 68), (64, 1), (32, 16), (20, 160), (8, 8), (2, 256)]
    (codeMat 84) (codeMat 161) (codeMat 161) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

end QiushiMatmul
