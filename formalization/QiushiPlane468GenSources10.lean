import QiushiPlane468GenData
import QiushiCertifiedTransport
import QiushiOrbit35FP
import QiushiStep99Orbit65Dispatch
import QiushiStep99Orbit69Dispatch
import QiushiStep99Orbit77Dispatch
import QiushiWcOrbit128Dispatch
import QiushiWcOrbit183Dispatch
import QiushiWcOrbit80Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane468GenSource0100 :
    QuotientRankAtLeast (spanCodes [292, 164, 84, 8, 2]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [384, 84, 32, 10, 1] [(292, 511), (164, 510), (84, 500), (8, 32), (2, 384)]
    (codeMat 84) (codeMat 500) (codeMat 94) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit183_lb15_wc

theorem plane468GenSource0101 :
    QuotientRankAtLeast (spanCodes [257, 130, 83, 33, 10, 7]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 164, 96, 16, 10, 1] [(257, 112), (130, 256), (83, 196), (33, 113), (10, 479), (7, 16)]
    (codeMat 334) (codeMat 205) (codeMat 242) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit69_lb15_unconditional

theorem plane468GenSource0102 :
    QuotientRankAtLeast (spanCodes [257, 130, 82, 32, 10, 6]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 128, 96, 20, 10, 1] [(257, 96), (130, 1), (82, 366), (32, 128), (10, 148), (6, 260)]
    (codeMat 85) (codeMat 330) (codeMat 394) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit77_lb15_unconditional

theorem plane468GenSource0103 :
    QuotientRankAtLeast (spanCodes [257, 130, 80, 34, 10, 4]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(257, 170), (130, 260), (80, 255), (34, 160), (10, 480), (4, 16)]
    (codeMat 143) (codeMat 233) (codeMat 233) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

theorem plane468GenSource0104 :
    QuotientRankAtLeast (spanCodes [292, 164, 84, 9, 3]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [384, 84, 32, 10, 1] [(292, 511), (164, 510), (84, 500), (9, 384), (3, 32)]
    (codeMat 84) (codeMat 500) (codeMat 94) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit183_lb15_wc

theorem plane468GenSource0105 :
    QuotientRankAtLeast (spanCodes [256, 132, 68, 32, 16, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(256, 2), (132, 20), (68, 148), (32, 1), (16, 8), (10, 104)]
    (codeMat 98) (codeMat 92) (codeMat 116) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane468GenSource0106 :
    QuotientRankAtLeast (spanCodes [292, 164, 64, 20, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [384, 96, 12, 2, 1] [(292, 384), (164, 385), (64, 2), (20, 398), (10, 495)]
    (codeMat 468) (codeMat 442) (codeMat 334) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit128_lb15_wc

theorem plane468GenSource0107 :
    QuotientRankAtLeast (spanCodes [262, 134, 65, 34, 21, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(262, 176), (134, 160), (65, 320), (34, 436), (21, 78), (10, 437)]
    (codeMat 354) (codeMat 465) (codeMat 465) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

theorem plane468GenSource0108 :
    QuotientRankAtLeast (spanCodes [258, 131, 64, 39, 20, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 96, 20, 10, 1] [(258, 378), (131, 180), (64, 432), (39, 356), (20, 191), (10, 420)]
    (codeMat 254) (codeMat 348) (codeMat 125) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit80_lb15_wc

theorem plane468GenSource0109 :
    QuotientRankAtLeast (spanCodes [260, 134, 67, 34, 23, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(260, 1), (134, 79), (67, 507), (34, 496), (23, 336), (10, 480)]
    (codeMat 213) (codeMat 159) (codeMat 230) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

end QiushiMatmul
