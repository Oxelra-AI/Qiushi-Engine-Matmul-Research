import QiushiPlane463GenData
import QiushiCertifiedTransport
import QiushiOrbit10FP
import QiushiOrbit14FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane463GenSource0200 :
    QuotientRankAtLeast (spanCodes [256, 129, 68, 36, 20, 8, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 9), (129, 413), (68, 126), (36, 8), (20, 264), (8, 384), (2, 360)]
    (codeMat 159) (codeMat 206) (codeMat 498) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane463GenSource0201 :
    QuotientRankAtLeast (spanCodes [257, 128, 68, 37, 20, 8, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(257, 21), (128, 9), (68, 23), (37, 381), (20, 97), (8, 511), (2, 8)]
    (codeMat 397) (codeMat 335) (codeMat 426) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane463GenSource0202 :
    QuotientRankAtLeast (spanCodes [257, 129, 68, 33, 16, 9, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(257, 71), (129, 258), (68, 70), (33, 440), (16, 16), (9, 432), (3, 256)]
    (codeMat 85) (codeMat 380) (codeMat 117) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane463GenSource0203 :
    QuotientRankAtLeast (spanCodes [256, 128, 68, 32, 16, 9, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(256, 1), (128, 2), (68, 70), (32, 8), (16, 16), (9, 432), (3, 256)]
    (codeMat 84) (codeMat 92) (codeMat 116) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane463GenSource0204 :
    QuotientRankAtLeast (spanCodes [260, 132, 68, 33, 21, 9, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(260, 384), (132, 387), (68, 385), (33, 503), (21, 105), (9, 511), (3, 130)]
    (codeMat 340) (codeMat 491) (codeMat 375) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane463GenSource0205 :
    QuotientRankAtLeast (spanCodes [256, 128, 68, 37, 21, 9, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 256), (128, 384), (68, 480), (37, 284), (21, 414), (9, 511), (3, 8)]
    (codeMat 270) (codeMat 473) (codeMat 409) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane463GenSource0206 :
    QuotientRankAtLeast (spanCodes [257, 129, 68, 36, 21, 9, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(257, 148), (129, 363), (68, 150), (36, 256), (21, 136), (9, 384), (3, 360)]
    (codeMat 213) (codeMat 346) (codeMat 459) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane463GenSource0207 :
    QuotientRankAtLeast (spanCodes [261, 133, 68, 33, 20, 9, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(261, 235), (133, 105), (68, 373), (33, 363), (20, 150), (9, 3), (3, 511)]
    (codeMat 491) (codeMat 425) (codeMat 249) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane463GenSource0208 :
    QuotientRankAtLeast (spanCodes [256, 128, 68, 36, 20, 9, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 2), (128, 3), (68, 150), (36, 128), (20, 136), (9, 384), (3, 360)]
    (codeMat 212) (codeMat 122) (codeMat 460) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane463GenSource0209 :
    QuotientRankAtLeast (spanCodes [257, 129, 68, 33, 17, 8, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(257, 227), (129, 97), (68, 284), (33, 224), (17, 96), (8, 256), (2, 8)]
    (codeMat 142) (codeMat 102) (codeMat 156) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

end QiushiMatmul
