import QiushiPlane465GenData
import QiushiCertifiedTransport
import QiushiOrbit29FP
import QiushiOrbit35FP
import QiushiStep99Orbit65Dispatch
import QiushiStep99Orbit76Dispatch
import QiushiWcOrbit80Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane465GenSource0030 :
    QuotientRankAtLeast (spanCodes [260, 150, 68, 52, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(260, 1), (150, 446), (68, 26), (52, 496), (10, 160), (1, 16)]
    (codeMat 205) (codeMat 156) (codeMat 102) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

theorem plane465GenSource0031 :
    QuotientRankAtLeast (spanCodes [273, 130, 67, 33, 10, 7]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [288, 160, 68, 20, 10, 1] [(273, 394), (130, 1), (67, 68), (33, 475), (10, 356), (7, 384)]
    (codeMat 117) (codeMat 102) (codeMat 156) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit76_lb15_unconditional

theorem plane465GenSource0032 :
    QuotientRankAtLeast (spanCodes [272, 131, 66, 32, 10, 6]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [288, 160, 68, 20, 10, 1] [(272, 78), (131, 319), (66, 228), (32, 1), (10, 452), (6, 384)]
    (codeMat 122) (codeMat 214) (codeMat 214) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit76_lb15_unconditional

theorem plane465GenSource0033 :
    QuotientRankAtLeast (spanCodes [257, 146, 66, 49, 10, 6]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 96, 20, 10, 1] [(257, 272), (146, 1), (66, 96), (49, 475), (10, 356), (6, 192)]
    (codeMat 103) (codeMat 98) (codeMat 140) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit80_lb15_wc

theorem plane465GenSource0034 :
    QuotientRankAtLeast (spanCodes [275, 128, 65, 35, 10, 5]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 96, 20, 10, 1] [(275, 270), (128, 1), (65, 260), (35, 191), (10, 356), (5, 192)]
    (codeMat 124) (codeMat 358) (codeMat 158) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit80_lb15_wc

theorem plane465GenSource0035 :
    QuotientRankAtLeast (spanCodes [259, 144, 64, 51, 10, 4]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [288, 160, 68, 20, 10, 1] [(259, 240), (144, 1), (64, 288), (51, 191), (10, 356), (4, 384)]
    (codeMat 110) (codeMat 354) (codeMat 142) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit76_lb15_unconditional

theorem plane465GenSource0036 :
    QuotientRankAtLeast (spanCodes [256, 128, 68, 32, 16, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160] [(256, 1), (128, 2), (68, 68), (32, 8), (16, 16), (10, 160)]
    (codeMat 84) (codeMat 84) (codeMat 84) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit29_lb15

theorem plane465GenSource0037 :
    QuotientRankAtLeast (spanCodes [256, 128, 68, 36, 20, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(256, 2), (128, 3), (68, 150), (36, 128), (20, 136), (10, 232)]
    (codeMat 212) (codeMat 122) (codeMat 460) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane465GenSource0038 :
    QuotientRankAtLeast (spanCodes [258, 130, 68, 39, 21, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 96, 20, 10, 1] [(258, 368), (130, 192), (68, 30), (39, 357), (21, 261), (10, 356)]
    (codeMat 179) (codeMat 169) (codeMat 225) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit80_lb15_wc

theorem plane465GenSource0039 :
    QuotientRankAtLeast (spanCodes [256, 128, 68, 38, 22, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(256, 8), (128, 9), (68, 104), (38, 28), (22, 31), (10, 252)]
    (codeMat 116) (codeMat 122) (codeMat 460) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

end QiushiMatmul
