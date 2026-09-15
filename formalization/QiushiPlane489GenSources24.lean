import QiushiPlane489GenData
import QiushiCertifiedTransport
import QiushiMonoOrbit43From14
import QiushiOrbit10FP
import QiushiOrbit11FP
import QiushiOrbit14FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane489GenSource0240 :
    QuotientRankAtLeast (spanCodes [256, 145, 81, 33, 8, 5, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 1), (145, 246), (81, 245), (33, 264), (8, 360), (5, 256), (2, 384)]
    (codeMat 92) (codeMat 213) (codeMat 470) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane489GenSource0241 :
    QuotientRankAtLeast (spanCodes [257, 128, 81, 49, 9, 5, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(257, 503), (128, 325), (81, 246), (49, 176), (9, 432), (5, 8), (3, 24)]
    (codeMat 142) (codeMat 494) (codeMat 501) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane489GenSource0242 :
    QuotientRankAtLeast (spanCodes [257, 144, 65, 53, 9, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 128, 32, 8, 2, 1] [(257, 441), (144, 3), (65, 9), (53, 162), (9, 8), (3, 130)]
    (codeMat 478) (codeMat 311) (codeMat 307) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit43_lb12_mono

theorem plane489GenSource0243 :
    QuotientRankAtLeast (spanCodes [256, 129, 64, 33, 8, 5, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(256, 3), (129, 20), (64, 2), (33, 208), (8, 128), (5, 8), (2, 32)]
    (codeMat 140) (codeMat 172) (codeMat 99) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane489GenSource0244 :
    QuotientRankAtLeast (spanCodes [256, 144, 81, 33, 8, 5, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 9), (144, 130), (81, 509), (33, 264), (8, 360), (5, 256), (2, 128)]
    (codeMat 95) (codeMat 85) (codeMat 340) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane489GenSource0245 :
    QuotientRankAtLeast (spanCodes [256, 144, 65, 49, 8, 5, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 511), (144, 130), (65, 9), (49, 104), (8, 8), (5, 384), (2, 128)]
    (codeMat 87) (codeMat 309) (codeMat 309) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane489GenSource0246 :
    QuotientRankAtLeast (spanCodes [256, 145, 65, 48, 8, 5, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 360), (145, 502), (65, 8), (48, 3), (8, 1), (5, 256), (2, 384)]
    (codeMat 106) (codeMat 405) (codeMat 407) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane489GenSource0247 :
    QuotientRankAtLeast (spanCodes [256, 129, 81, 48, 8, 5, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 360), (129, 480), (81, 28), (48, 1), (8, 3), (5, 384), (2, 256)]
    (codeMat 106) (codeMat 397) (codeMat 250) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane489GenSource0248 :
    QuotientRankAtLeast (spanCodes [256, 145, 81, 33, 8, 4, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 128), (145, 29), (81, 413), (33, 149), (8, 360), (4, 2), (2, 3)]
    (codeMat 305) (codeMat 115) (codeMat 492) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane489GenSource0249 :
    QuotientRankAtLeast (spanCodes [258, 135, 71, 34, 18, 10]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 128, 32, 8, 2, 1] [(258, 411), (135, 274), (71, 283), (34, 435), (18, 432), (10, 433)]
    (codeMat 370) (codeMat 477) (codeMat 431) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit43_lb12_mono

end QiushiMatmul
