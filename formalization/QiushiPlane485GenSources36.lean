import QiushiPlane485GenData
import QiushiCertifiedTransport
import QiushiOrbit10FP
import QiushiOrbit11FP
import QiushiOrbit14FP
import QiushiOrbit23FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane485GenSource0360 :
    QuotientRankAtLeast (spanCodes [257, 160, 64, 17, 8, 5, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(257, 127), (160, 28), (64, 9), (17, 96), (8, 8), (5, 384), (2, 256)]
    (codeMat 86) (codeMat 421) (codeMat 179) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane485GenSource0361 :
    QuotientRankAtLeast (spanCodes [321, 128, 32, 17, 8, 5, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(321, 69), (128, 128), (32, 32), (17, 21), (8, 40), (5, 1), (2, 2)]
    (codeMat 273) (codeMat 337) (codeMat 337) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane485GenSource0362 :
    QuotientRankAtLeast (spanCodes [448, 33, 17, 8, 5, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 4, 8, 80, 128] [(448, 4), (33, 90), (17, 82), (8, 9), (5, 130), (2, 128)]
    (codeMat 266) (codeMat 425) (codeMat 249) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit23_lb12

theorem plane485GenSource0363 :
    QuotientRankAtLeast (spanCodes [256, 129, 64, 36, 20, 9, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(256, 3), (129, 69), (64, 1), (36, 24), (20, 424), (9, 8), (3, 256)]
    (codeMat 92) (codeMat 167) (codeMat 167) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane485GenSource0364 :
    QuotientRankAtLeast (spanCodes [260, 132, 64, 37, 20, 9, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(260, 360), (132, 363), (64, 1), (37, 97), (20, 235), (9, 8), (3, 511)]
    (codeMat 412) (codeMat 405) (codeMat 407) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane485GenSource0365 :
    QuotientRankAtLeast (spanCodes [261, 132, 69, 33, 20, 9, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(261, 119), (132, 483), (69, 126), (33, 392), (20, 480), (9, 384), (3, 360)]
    (codeMat 214) (codeMat 382) (codeMat 499) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane485GenSource0366 :
    QuotientRankAtLeast (spanCodes [256, 133, 65, 33, 20, 9, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(256, 325), (133, 71), (65, 3), (33, 424), (20, 184), (9, 24), (3, 256)]
    (codeMat 93) (codeMat 415) (codeMat 253) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane485GenSource0367 :
    QuotientRankAtLeast (spanCodes [261, 128, 65, 33, 20, 9, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(261, 71), (128, 325), (65, 1), (33, 440), (20, 168), (9, 8), (3, 256)]
    (codeMat 93) (codeMat 423) (codeMat 181) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane485GenSource0368 :
    QuotientRankAtLeast (spanCodes [288, 161, 96, 16, 9, 4, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(288, 3), (161, 500), (96, 326), (16, 256), (9, 432), (4, 24), (3, 16)]
    (codeMat 142) (codeMat 236) (codeMat 123) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane485GenSource0369 :
    QuotientRankAtLeast (spanCodes [288, 160, 97, 16, 9, 4, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(288, 1), (160, 324), (97, 502), (16, 256), (9, 432), (4, 8), (3, 16)]
    (codeMat 142) (codeMat 204) (codeMat 114) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

end QiushiMatmul
