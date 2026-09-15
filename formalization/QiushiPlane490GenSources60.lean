import QiushiPlane490GenData
import QiushiCertifiedTransport
import QiushiOrbit10FP
import QiushiOrbit11FP
import QiushiOrbit14FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane490GenSource0600 :
    QuotientRankAtLeast (spanCodes [260, 132, 69, 32, 21, 8, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(260, 2), (132, 509), (69, 150), (32, 128), (21, 96), (8, 384), (2, 360)]
    (codeMat 157) (codeMat 234) (codeMat 461) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane490GenSource0601 :
    QuotientRankAtLeast (spanCodes [256, 133, 64, 32, 17, 8, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(256, 3), (133, 68), (64, 2), (32, 24), (17, 160), (8, 16), (2, 256)]
    (codeMat 84) (codeMat 172) (codeMat 99) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane490GenSource0602 :
    QuotientRankAtLeast (spanCodes [273, 144, 81, 49, 8, 4, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(273, 161), (144, 3), (81, 484), (49, 160), (8, 256), (4, 8), (2, 24)]
    (codeMat 142) (codeMat 86) (codeMat 212) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane490GenSource0603 :
    QuotientRankAtLeast (spanCodes [256, 128, 97, 17, 8, 4, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(256, 3), (128, 2), (97, 228), (17, 160), (8, 256), (4, 24), (2, 16)]
    (codeMat 140) (codeMat 116) (codeMat 92) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane490GenSource0604 :
    QuotientRankAtLeast (spanCodes [273, 145, 80, 48, 8, 5, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(273, 254), (145, 246), (80, 30), (48, 1), (8, 3), (5, 256), (2, 384)]
    (codeMat 98) (codeMat 445) (codeMat 478) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane490GenSource0605 :
    QuotientRankAtLeast (spanCodes [256, 193, 33, 17, 8, 5, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(256, 128), (193, 248), (33, 42), (17, 28), (8, 63), (5, 40), (2, 32)]
    (codeMat 267) (codeMat 233) (codeMat 233) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane490GenSource0606 :
    QuotientRankAtLeast (spanCodes [261, 133, 65, 36, 21, 9, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(261, 276), (133, 235), (65, 130), (36, 256), (21, 232), (9, 128), (3, 8)]
    (codeMat 206) (codeMat 282) (codeMat 267) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane490GenSource0607 :
    QuotientRankAtLeast (spanCodes [256, 128, 69, 32, 16, 9, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(256, 3), (128, 2), (69, 326), (32, 24), (16, 16), (9, 432), (3, 256)]
    (codeMat 84) (codeMat 124) (codeMat 124) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane490GenSource0608 :
    QuotientRankAtLeast (spanCodes [257, 129, 64, 37, 17, 9, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(257, 112), (129, 88), (64, 8), (37, 70), (17, 131), (9, 1), (3, 128)]
    (codeMat 99) (codeMat 307) (codeMat 311) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane490GenSource0609 :
    QuotientRankAtLeast (spanCodes [257, 128, 65, 37, 17, 9, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(257, 240), (128, 8), (65, 216), (37, 198), (17, 129), (9, 3), (3, 128)]
    (codeMat 99) (codeMat 299) (codeMat 318) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

end QiushiMatmul
