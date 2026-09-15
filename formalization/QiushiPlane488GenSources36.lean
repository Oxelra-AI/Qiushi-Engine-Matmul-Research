import QiushiPlane488GenData
import QiushiCertifiedTransport
import QiushiOrbit10FP
import QiushiOrbit11FP
import QiushiOrbit14FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane488GenSource0360 :
    QuotientRankAtLeast (spanCodes [260, 133, 68, 36, 17, 8, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(260, 3), (133, 68), (68, 326), (36, 24), (17, 160), (8, 432), (2, 256)]
    (codeMat 93) (codeMat 236) (codeMat 123) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane488GenSource0361 :
    QuotientRankAtLeast (spanCodes [261, 133, 69, 37, 17, 8, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(261, 71), (133, 68), (69, 70), (37, 440), (17, 160), (8, 432), (2, 256)]
    (codeMat 92) (codeMat 492) (codeMat 115) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane488GenSource0362 :
    QuotientRankAtLeast (spanCodes [257, 133, 65, 33, 17, 8, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(257, 327), (133, 68), (65, 2), (33, 184), (17, 160), (8, 16), (2, 256)]
    (codeMat 85) (codeMat 428) (codeMat 107) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane488GenSource0363 :
    QuotientRankAtLeast (spanCodes [273, 144, 81, 49, 8, 4, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(273, 161), (144, 3), (81, 484), (49, 160), (8, 256), (4, 8), (2, 24)]
    (codeMat 142) (codeMat 86) (codeMat 212) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane488GenSource0364 :
    QuotientRankAtLeast (spanCodes [288, 129, 96, 17, 8, 4, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(288, 1), (129, 162), (96, 324), (17, 160), (8, 256), (4, 8), (2, 16)]
    (codeMat 142) (codeMat 84) (codeMat 84) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane488GenSource0365 :
    QuotientRankAtLeast (spanCodes [273, 145, 81, 49, 8, 5, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(273, 247), (145, 246), (81, 245), (49, 264), (8, 360), (5, 128), (2, 384)]
    (codeMat 92) (codeMat 501) (codeMat 494) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane488GenSource0366 :
    QuotientRankAtLeast (spanCodes [288, 128, 96, 17, 8, 5, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(288, 325), (128, 2), (96, 324), (17, 160), (8, 256), (5, 8), (2, 16)]
    (codeMat 140) (codeMat 340) (codeMat 85) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane488GenSource0367 :
    QuotientRankAtLeast (spanCodes [256, 132, 68, 36, 21, 9, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(256, 1), (132, 70), (68, 68), (36, 8), (21, 240), (9, 32), (3, 128)]
    (codeMat 92) (codeMat 212) (codeMat 86) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane488GenSource0368 :
    QuotientRankAtLeast (spanCodes [261, 133, 64, 32, 21, 9, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(261, 326), (133, 327), (64, 3), (32, 432), (21, 184), (9, 24), (3, 256)]
    (codeMat 92) (codeMat 443) (codeMat 254) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane488GenSource0369 :
    QuotientRankAtLeast (spanCodes [257, 129, 64, 32, 21, 9, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(257, 70), (129, 69), (64, 1), (32, 432), (21, 168), (9, 8), (3, 256)]
    (codeMat 92) (codeMat 419) (codeMat 183) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

end QiushiMatmul
