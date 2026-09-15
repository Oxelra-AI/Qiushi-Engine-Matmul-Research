import QiushiPlane491GenData
import QiushiCertifiedTransport
import QiushiOrbit10FP
import QiushiOrbit11FP
import QiushiOrbit14FP
import QiushiOrbit25FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane491GenSource0540 :
    QuotientRankAtLeast (spanCodes [257, 129, 68, 33, 16, 9, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(257, 71), (129, 258), (68, 70), (33, 440), (16, 16), (9, 432), (3, 256)]
    (codeMat 85) (codeMat 380) (codeMat 117) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane491GenSource0541 :
    QuotientRankAtLeast (spanCodes [256, 132, 64, 36, 20, 9, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(256, 1), (132, 71), (64, 3), (36, 8), (20, 440), (9, 24), (3, 256)]
    (codeMat 92) (codeMat 159) (codeMat 230) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane491GenSource0542 :
    QuotientRankAtLeast (spanCodes [261, 128, 65, 32, 21, 9, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(261, 70), (128, 325), (65, 1), (32, 432), (21, 168), (9, 8), (3, 256)]
    (codeMat 93) (codeMat 419) (codeMat 183) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane491GenSource0543 :
    QuotientRankAtLeast (spanCodes [261, 128, 69, 32, 17, 13, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(261, 70), (128, 3), (69, 71), (32, 432), (17, 280), (13, 440), (3, 256)]
    (codeMat 92) (codeMat 379) (codeMat 247) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane491GenSource0544 :
    QuotientRankAtLeast (spanCodes [257, 132, 69, 36, 17, 13, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(257, 252), (132, 278), (69, 483), (36, 256), (17, 232), (13, 480), (3, 360)]
    (codeMat 214) (codeMat 409) (codeMat 473) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane491GenSource0545 :
    QuotientRankAtLeast (spanCodes [268, 140, 76, 44, 24, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 4, 8, 80, 256] [(268, 349), (140, 93), (76, 89), (44, 341), (24, 5), (3, 2)]
    (codeMat 270) (codeMat 249) (codeMat 425) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit25_lb12

theorem plane491GenSource0546 :
    QuotientRankAtLeast (spanCodes [257, 133, 65, 37, 21, 9, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(257, 353), (133, 413), (65, 9), (37, 97), (21, 414), (9, 8), (3, 130)]
    (codeMat 478) (codeMat 275) (codeMat 275) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane491GenSource0547 :
    QuotientRankAtLeast (spanCodes [256, 133, 65, 37, 21, 8, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(256, 325), (133, 71), (65, 3), (37, 424), (21, 440), (8, 24), (3, 256)]
    (codeMat 85) (codeMat 415) (codeMat 253) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane491GenSource0548 :
    QuotientRankAtLeast (spanCodes [256, 132, 68, 36, 16, 12, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(256, 3), (132, 196), (68, 198), (36, 216), (16, 32), (12, 240), (3, 128)]
    (codeMat 84) (codeMat 236) (codeMat 123) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane491GenSource0549 :
    QuotientRankAtLeast (spanCodes [256, 133, 64, 36, 20, 9, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(256, 2), (133, 68), (64, 3), (36, 16), (20, 416), (9, 24), (2, 256)]
    (codeMat 92) (codeMat 169) (codeMat 225) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

end QiushiMatmul
