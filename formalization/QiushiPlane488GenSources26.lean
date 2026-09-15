import QiushiPlane488GenData
import QiushiCertifiedTransport
import QiushiMonoOrbit149From65
import QiushiOrbit35FP
import QiushiStep128Mono190From72
import QiushiStep99Orbit65Dispatch
import QiushiWcOrbit220Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane488GenSource0260 :
    QuotientRankAtLeast (spanCodes [260, 149, 71, 39, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [324, 128, 32, 10, 1] [(260, 128), (149, 463), (71, 484), (39, 367), (10, 366)]
    (codeMat 379) (codeMat 185) (codeMat 481) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit190_lb15_mono

theorem plane488GenSource0261 :
    QuotientRankAtLeast (spanCodes [256, 131, 67, 35, 22, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(256, 9), (131, 104), (67, 96), (35, 31), (22, 252), (10, 224)]
    (codeMat 124) (codeMat 244) (codeMat 95) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane488GenSource0262 :
    QuotientRankAtLeast (spanCodes [258, 132, 71, 39, 23, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(258, 150), (132, 148), (71, 151), (39, 232), (23, 104), (10, 224)]
    (codeMat 157) (codeMat 489) (codeMat 241) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane488GenSource0263 :
    QuotientRankAtLeast (spanCodes [257, 130, 64, 32, 21, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(257, 245), (130, 260), (64, 27), (32, 320), (21, 176), (10, 480)]
    (codeMat 159) (codeMat 397) (codeMat 250) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

theorem plane488GenSource0264 :
    QuotientRankAtLeast (spanCodes [256, 128, 70, 38, 16, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(256, 3), (128, 1), (70, 148), (38, 136), (16, 8), (10, 104)]
    (codeMat 212) (codeMat 102) (codeMat 156) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane488GenSource0265 :
    QuotientRankAtLeast (spanCodes [261, 130, 65, 33, 16, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(261, 96), (130, 1), (65, 8), (33, 224), (16, 3), (10, 28)]
    (codeMat 125) (codeMat 266) (codeMat 266) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane488GenSource0266 :
    QuotientRankAtLeast (spanCodes [288, 135, 96, 17, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 68, 16, 10, 1] [(288, 27), (135, 272), (96, 283), (17, 78), (10, 79)]
    (codeMat 299) (codeMat 253) (codeMat 415) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit149_lb15_mono

theorem plane488GenSource0267 :
    QuotientRankAtLeast (spanCodes [259, 178, 96, 10, 7]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [334, 192, 36, 16, 1] [(259, 208), (178, 228), (96, 363), (10, 398), (7, 16)]
    (codeMat 334) (codeMat 254) (codeMat 443) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit220_lb15_wc

theorem plane488GenSource0268 :
    QuotientRankAtLeast (spanCodes [274, 129, 66, 34, 10, 7]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(274, 78), (129, 255), (66, 228), (34, 496), (10, 480), (7, 320)]
    (codeMat 87) (codeMat 498) (codeMat 206) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

theorem plane488GenSource0269 :
    QuotientRankAtLeast (spanCodes [261, 128, 69, 37, 23, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(261, 96), (128, 9), (69, 104), (37, 224), (23, 31), (10, 252)]
    (codeMat 116) (codeMat 346) (codeMat 459) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

end QiushiMatmul
