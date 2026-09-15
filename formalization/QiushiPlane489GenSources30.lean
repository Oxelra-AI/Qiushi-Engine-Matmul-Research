import QiushiPlane489GenData
import QiushiCertifiedTransport
import QiushiOrbit11FP
import QiushiOrbit14FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane489GenSource0300 :
    QuotientRankAtLeast (spanCodes [256, 145, 80, 49, 8, 4, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 130), (145, 374), (80, 245), (49, 96), (8, 360), (4, 128), (2, 384)]
    (codeMat 93) (codeMat 241) (codeMat 489) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane489GenSource0301 :
    QuotientRankAtLeast (spanCodes [256, 145, 80, 48, 8, 5, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 360), (145, 28), (80, 480), (48, 384), (8, 256), (5, 1), (2, 3)]
    (codeMat 177) (codeMat 342) (codeMat 215) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane489GenSource0302 :
    QuotientRankAtLeast (spanCodes [256, 144, 81, 48, 8, 5, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 360), (144, 8), (81, 502), (48, 256), (8, 384), (5, 3), (2, 1)]
    (codeMat 177) (codeMat 334) (codeMat 442) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane489GenSource0303 :
    QuotientRankAtLeast (spanCodes [256, 144, 80, 49, 8, 5, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 384), (144, 8), (80, 264), (49, 509), (8, 360), (5, 3), (2, 1)]
    (codeMat 305) (codeMat 355) (codeMat 190) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane489GenSource0304 :
    QuotientRankAtLeast (spanCodes [256, 129, 65, 49, 8, 5, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(256, 54), (129, 61), (65, 2), (49, 208), (8, 128), (5, 32), (2, 40)]
    (codeMat 141) (codeMat 426) (codeMat 335) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane489GenSource0305 :
    QuotientRankAtLeast (spanCodes [256, 145, 65, 33, 8, 5, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(256, 219), (145, 52), (65, 130), (33, 208), (8, 128), (5, 8), (2, 32)]
    (codeMat 143) (codeMat 172) (codeMat 99) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane489GenSource0306 :
    QuotientRankAtLeast (spanCodes [256, 193, 33, 17, 8, 5, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(256, 128), (193, 248), (33, 42), (17, 28), (8, 63), (5, 40), (2, 32)]
    (codeMat 267) (codeMat 233) (codeMat 233) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane489GenSource0307 :
    QuotientRankAtLeast (spanCodes [257, 129, 68, 36, 20, 9, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(257, 100), (129, 191), (68, 109), (36, 32), (20, 248), (9, 40), (3, 128)]
    (codeMat 94) (codeMat 467) (codeMat 339) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane489GenSource0308 :
    QuotientRankAtLeast (spanCodes [257, 132, 68, 33, 20, 9, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(257, 198), (132, 71), (68, 197), (33, 240), (20, 120), (9, 40), (3, 128)]
    (codeMat 93) (codeMat 499) (codeMat 382) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane489GenSource0309 :
    QuotientRankAtLeast (spanCodes [257, 129, 64, 48, 9, 4, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(257, 28), (129, 30), (64, 3), (48, 128), (9, 216), (4, 32), (3, 40)]
    (codeMat 140) (codeMat 409) (codeMat 473) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

end QiushiMatmul
