import QiushiPlane474GenData
import QiushiCertifiedTransport
import QiushiOrbit35FP
import QiushiStep99Orbit65Dispatch
import QiushiStep99Orbit69Dispatch
import QiushiStep99Orbit76Dispatch
import QiushiStep99Orbit77Dispatch
import QiushiWcOrbit141Dispatch
import QiushiWcOrbit80Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane474GenSource0070 :
    QuotientRankAtLeast (spanCodes [259, 133, 64, 37, 20, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [288, 160, 68, 20, 10, 1] [(259, 452), (133, 453), (64, 384), (37, 414), (20, 81), (10, 308)]
    (codeMat 285) (codeMat 124) (codeMat 124) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit76_lb15_unconditional

theorem plane474GenSource0071 :
    QuotientRankAtLeast (spanCodes [259, 132, 65, 37, 21, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 128, 96, 20, 10, 1] [(259, 30), (132, 21), (65, 1), (37, 356), (21, 484), (10, 127)]
    (codeMat 165) (codeMat 407) (codeMat 405) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit77_lb15_unconditional

theorem plane474GenSource0072 :
    QuotientRankAtLeast (spanCodes [261, 128, 67, 35, 23, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 96, 20, 10, 1] [(261, 31), (128, 260), (67, 452), (35, 464), (23, 378), (10, 453)]
    (codeMat 279) (codeMat 163) (codeMat 165) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit80_lb15_wc

theorem plane474GenSource0073 :
    QuotientRankAtLeast (spanCodes [294, 160, 65, 21, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [264, 84, 32, 2, 1] [(294, 349), (160, 350), (65, 2), (21, 265), (10, 383)]
    (codeMat 253) (codeMat 426) (codeMat 335) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit141_lb15_wc

theorem plane474GenSource0074 :
    QuotientRankAtLeast (spanCodes [259, 132, 64, 37, 20, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 96, 20, 10, 1] [(259, 283), (132, 223), (64, 260), (37, 170), (20, 367), (10, 378)]
    (codeMat 279) (codeMat 501) (codeMat 494) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit80_lb15_wc

theorem plane474GenSource0075 :
    QuotientRankAtLeast (spanCodes [262, 131, 66, 32, 22, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 164, 96, 16, 10, 1] [(262, 436), (131, 222), (66, 363), (32, 256), (22, 272), (10, 368)]
    (codeMat 157) (codeMat 409) (codeMat 473) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit69_lb15_unconditional

theorem plane474GenSource0076 :
    QuotientRankAtLeast (spanCodes [257, 130, 68, 39, 16, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(257, 150), (130, 1), (68, 148), (39, 232), (16, 8), (10, 104)]
    (codeMat 213) (codeMat 354) (codeMat 142) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane474GenSource0077 :
    QuotientRankAtLeast (spanCodes [273, 130, 81, 50, 10, 5]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(273, 158), (130, 3), (81, 28), (50, 232), (10, 224), (5, 128)]
    (codeMat 85) (codeMat 370) (codeMat 207) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane474GenSource0078 :
    QuotientRankAtLeast (spanCodes [294, 166, 70, 18, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(294, 437), (166, 245), (70, 69), (18, 27), (10, 11), (1, 1)]
    (codeMat 273) (codeMat 307) (codeMat 311) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

theorem plane474GenSource0079 :
    QuotientRankAtLeast (spanCodes [262, 131, 65, 32, 21, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(262, 437), (131, 78), (65, 1), (32, 320), (21, 160), (10, 496)]
    (codeMat 157) (codeMat 405) (codeMat 407) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

end QiushiMatmul
