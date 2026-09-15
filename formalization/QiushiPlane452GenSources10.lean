import QiushiPlane452GenData
import QiushiCertifiedTransport
import QiushiOrbit14FP
import QiushiStep81Qdim2Generated
import QiushiWcOrbit80Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane452GenSource0100 :
    QuotientRankAtLeast (spanCodes [256, 135, 68, 35, 20, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 96, 20, 10, 1] [(256, 432), (135, 420), (68, 160), (35, 378), (20, 367), (10, 170)]
    (codeMat 334) (codeMat 442) (codeMat 334) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit80_lb15_wc

theorem plane452GenSource0101 :
    QuotientRankAtLeast (spanCodes [257, 132, 65, 35, 20, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 96, 20, 10, 1] [(257, 180), (132, 20), (65, 260), (35, 191), (20, 21), (10, 453)]
    (codeMat 334) (codeMat 103) (codeMat 188) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit80_lb15_wc

theorem plane452GenSource0102 :
    QuotientRankAtLeast (spanCodes [256, 134, 66, 35, 20, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 96, 20, 10, 1] [(256, 260), (134, 261), (66, 96), (35, 170), (20, 453), (10, 464)]
    (codeMat 277) (codeMat 460) (codeMat 122) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit80_lb15_wc

theorem plane452GenSource0103 :
    QuotientRankAtLeast (spanCodes [256, 130, 71, 35, 20, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 96, 20, 10, 1] [(256, 260), (130, 432), (71, 420), (35, 453), (20, 378), (10, 367)]
    (codeMat 271) (codeMat 477) (codeMat 431) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit80_lb15_wc

theorem plane452GenSource0104 :
    QuotientRankAtLeast (spanCodes [260, 129, 64, 35, 20, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 96, 20, 10, 1] [(260, 1), (129, 357), (64, 260), (35, 367), (20, 21), (10, 170)]
    (codeMat 277) (codeMat 85) (codeMat 340) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit80_lb15_wc

theorem plane452GenSource0105 :
    QuotientRankAtLeast (spanCodes [259, 131, 70, 35, 20, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 96, 20, 10, 1] [(259, 96), (131, 356), (70, 97), (35, 464), (20, 378), (10, 191)]
    (codeMat 277) (codeMat 379) (codeMat 247) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit80_lb15_wc

theorem plane452GenSource0106 :
    QuotientRankAtLeast (spanCodes [262, 134, 71, 35, 20, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 96, 20, 10, 1] [(262, 160), (134, 272), (71, 180), (35, 170), (20, 464), (10, 191)]
    (codeMat 334) (codeMat 169) (codeMat 225) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit80_lb15_wc

theorem plane452GenSource0107 :
    QuotientRankAtLeast (spanCodes [263, 132, 68, 35, 20, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 96, 20, 10, 1] [(263, 261), (132, 96), (68, 356), (35, 453), (20, 464), (10, 378)]
    (codeMat 277) (codeMat 409) (codeMat 473) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit80_lb15_wc

theorem plane452GenSource0108 :
    QuotientRankAtLeast (spanCodes [256, 130, 67, 35, 17, 10, 5]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 68, 32, 20, 10, 1] [(256, 1), (130, 390), (67, 323), (35, 328), (17, 240), (10, 408), (5, 128)]
    (codeMat 84) (codeMat 157) (codeMat 486) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step81o17s4Span_lb

theorem plane452GenSource0109 :
    QuotientRankAtLeast (spanCodes [258, 130, 64, 34, 20, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(258, 257), (130, 256), (64, 2), (34, 105), (20, 97), (10, 406), (1, 130)]
    (codeMat 348) (codeMat 396) (codeMat 106) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

end QiushiMatmul
