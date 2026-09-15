import QiushiPlane452GenData
import QiushiCertifiedTransport
import QiushiOrbit31FP
import QiushiWcOrbit80Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane452GenSource0090 :
    QuotientRankAtLeast (spanCodes [322, 34, 16, 10, 4, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68] [(322, 80), (34, 20), (16, 2), (10, 21), (4, 32), (1, 40)]
    (codeMat 266) (codeMat 337) (codeMat 337) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit31_lb15

theorem plane452GenSource0091 :
    QuotientRankAtLeast (spanCodes [259, 134, 69, 35, 20, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 96, 20, 10, 1] [(259, 452), (134, 223), (69, 31), (35, 453), (20, 367), (10, 464)]
    (codeMat 286) (codeMat 156) (codeMat 102) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit80_lb15_wc

theorem plane452GenSource0092 :
    QuotientRankAtLeast (spanCodes [258, 132, 70, 35, 20, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 96, 20, 10, 1] [(258, 160), (132, 272), (70, 180), (35, 170), (20, 464), (10, 191)]
    (codeMat 271) (codeMat 169) (codeMat 225) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit80_lb15_wc

theorem plane452GenSource0093 :
    QuotientRankAtLeast (spanCodes [259, 130, 64, 35, 20, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 96, 20, 10, 1] [(259, 20), (130, 260), (64, 432), (35, 21), (20, 453), (10, 378)]
    (codeMat 334) (codeMat 206) (codeMat 498) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit80_lb15_wc

theorem plane452GenSource0094 :
    QuotientRankAtLeast (spanCodes [258, 128, 67, 35, 20, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 96, 20, 10, 1] [(258, 357), (128, 260), (67, 261), (35, 21), (20, 170), (10, 453)]
    (codeMat 277) (codeMat 226) (codeMat 141) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit80_lb15_wc

theorem plane452GenSource0095 :
    QuotientRankAtLeast (spanCodes [263, 129, 71, 35, 20, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 96, 20, 10, 1] [(263, 223), (129, 31), (71, 475), (35, 367), (20, 464), (10, 21)]
    (codeMat 286) (codeMat 313) (codeMat 313) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit80_lb15_wc

theorem plane452GenSource0096 :
    QuotientRankAtLeast (spanCodes [257, 129, 66, 35, 20, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 96, 20, 10, 1] [(257, 420), (129, 160), (66, 272), (35, 367), (20, 170), (10, 464)]
    (codeMat 271) (codeMat 372) (codeMat 93) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit80_lb15_wc

theorem plane452GenSource0097 :
    QuotientRankAtLeast (spanCodes [260, 128, 70, 35, 20, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 96, 20, 10, 1] [(260, 260), (128, 432), (70, 420), (35, 453), (20, 378), (10, 367)]
    (codeMat 334) (codeMat 477) (codeMat 431) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit80_lb15_wc

theorem plane452GenSource0098 :
    QuotientRankAtLeast (spanCodes [261, 130, 69, 35, 20, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 96, 20, 10, 1] [(261, 97), (130, 1), (69, 357), (35, 191), (20, 367), (10, 21)]
    (codeMat 277) (codeMat 302) (codeMat 302) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit80_lb15_wc

theorem plane452GenSource0099 :
    QuotientRankAtLeast (spanCodes [261, 134, 64, 35, 20, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 96, 20, 10, 1] [(261, 180), (134, 20), (64, 260), (35, 191), (20, 21), (10, 453)]
    (codeMat 271) (codeMat 103) (codeMat 188) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit80_lb15_wc

end QiushiMatmul
