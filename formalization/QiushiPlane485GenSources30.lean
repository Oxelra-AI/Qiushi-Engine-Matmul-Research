import QiushiPlane485GenData
import QiushiCertifiedTransport
import QiushiOrbit10FP
import QiushiOrbit11FP
import QiushiOrbit14FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane485GenSource0300 :
    QuotientRankAtLeast (spanCodes [288, 128, 96, 17, 8, 5, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(288, 325), (128, 2), (96, 324), (17, 160), (8, 256), (5, 8), (2, 16)]
    (codeMat 140) (codeMat 340) (codeMat 85) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane485GenSource0301 :
    QuotientRankAtLeast (spanCodes [290, 162, 64, 18, 10, 6, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(290, 503), (162, 502), (64, 2), (18, 432), (10, 176), (6, 8), (1, 16)]
    (codeMat 140) (codeMat 444) (codeMat 110) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane485GenSource0302 :
    QuotientRankAtLeast (spanCodes [288, 160, 64, 18, 10, 6, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(288, 325), (160, 326), (64, 2), (18, 432), (10, 176), (6, 24), (1, 16)]
    (codeMat 140) (codeMat 412) (codeMat 111) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane485GenSource0303 :
    QuotientRankAtLeast (spanCodes [260, 133, 65, 32, 20, 8, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(260, 2), (133, 324), (65, 3), (32, 16), (20, 160), (8, 24), (2, 256)]
    (codeMat 85) (codeMat 169) (codeMat 225) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane485GenSource0304 :
    QuotientRankAtLeast (spanCodes [257, 129, 64, 33, 20, 9, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(257, 71), (129, 69), (64, 1), (33, 440), (20, 168), (9, 8), (3, 256)]
    (codeMat 92) (codeMat 423) (codeMat 181) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane485GenSource0305 :
    QuotientRankAtLeast (spanCodes [260, 132, 64, 33, 20, 9, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(260, 325), (132, 327), (64, 3), (33, 424), (20, 184), (9, 24), (3, 256)]
    (codeMat 92) (codeMat 415) (codeMat 253) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane485GenSource0306 :
    QuotientRankAtLeast (spanCodes [260, 128, 68, 33, 20, 9, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(260, 511), (128, 3), (68, 510), (33, 392), (20, 480), (9, 384), (3, 360)]
    (codeMat 212) (codeMat 382) (codeMat 499) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane485GenSource0307 :
    QuotientRankAtLeast (spanCodes [257, 132, 68, 33, 20, 9, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(257, 198), (132, 71), (68, 197), (33, 240), (20, 120), (9, 40), (3, 128)]
    (codeMat 93) (codeMat 499) (codeMat 382) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane485GenSource0308 :
    QuotientRankAtLeast (spanCodes [256, 132, 64, 36, 20, 9, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(256, 1), (132, 71), (64, 3), (36, 8), (20, 440), (9, 24), (3, 256)]
    (codeMat 92) (codeMat 159) (codeMat 230) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane485GenSource0309 :
    QuotientRankAtLeast (spanCodes [261, 133, 64, 33, 20, 8, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(261, 361), (133, 362), (64, 1), (33, 105), (20, 284), (8, 8), (2, 511)]
    (codeMat 468) (codeMat 403) (codeMat 403) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

end QiushiMatmul
