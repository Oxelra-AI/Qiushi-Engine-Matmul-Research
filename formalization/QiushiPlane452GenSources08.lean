import QiushiPlane452GenData
import QiushiCertifiedTransport
import QiushiMonoOrbit95From31
import QiushiOrbit31FP
import QiushiWcOrbit201Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane452GenSource0080 :
    QuotientRankAtLeast (spanCodes [388, 67, 35, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [340, 132, 32, 10, 1] [(388, 497), (67, 496), (35, 133), (20, 175), (10, 464)]
    (codeMat 477) (codeMat 412) (codeMat 111) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit201_lb16_wc

theorem plane452GenSource0081 :
    QuotientRankAtLeast (spanCodes [32, 20, 8, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [32, 20, 8, 2, 1] [(32, 2), (20, 20), (8, 1), (2, 32), (1, 8)]
    (codeMat 266) (codeMat 161) (codeMat 161) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit95_lb15_mono

theorem plane452GenSource0082 :
    QuotientRankAtLeast (spanCodes [34, 16, 10, 4, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [32, 20, 8, 2, 1] [(34, 20), (16, 2), (10, 21), (4, 32), (1, 40)]
    (codeMat 266) (codeMat 337) (codeMat 337) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit95_lb15_mono

theorem plane452GenSource0083 :
    QuotientRankAtLeast (spanCodes [33, 16, 8, 4, 2]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [32, 20, 8, 2, 1] [(33, 20), (16, 1), (8, 2), (4, 32), (2, 8)]
    (codeMat 266) (codeMat 266) (codeMat 266) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit95_lb15_mono

theorem plane452GenSource0084 :
    QuotientRankAtLeast (spanCodes [32, 17, 9, 5, 3]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [32, 20, 8, 2, 1] [(32, 2), (17, 62), (9, 63), (5, 40), (3, 8)]
    (codeMat 266) (codeMat 249) (codeMat 425) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit95_lb15_mono

theorem plane452GenSource0085 :
    QuotientRankAtLeast (spanCodes [32, 16, 9, 4, 3]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [32, 20, 8, 2, 1] [(32, 1), (16, 2), (9, 54), (4, 8), (3, 32)]
    (codeMat 266) (codeMat 92) (codeMat 116) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit95_lb15_mono

theorem plane452GenSource0086 :
    QuotientRankAtLeast (spanCodes [33, 17, 8, 5, 2]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [32, 20, 8, 2, 1] [(33, 30), (17, 28), (8, 3), (5, 40), (2, 32)]
    (codeMat 266) (codeMat 425) (codeMat 249) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit95_lb15_mono

theorem plane452GenSource0087 :
    QuotientRankAtLeast (spanCodes [34, 18, 10, 6, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [32, 20, 8, 2, 1] [(34, 62), (18, 63), (10, 60), (6, 8), (1, 32)]
    (codeMat 266) (codeMat 498) (codeMat 206) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit95_lb15_mono

theorem plane452GenSource0088 :
    QuotientRankAtLeast (spanCodes [193, 32, 17, 9, 5, 3]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68] [(193, 120), (32, 2), (17, 62), (9, 63), (5, 40), (3, 8)]
    (codeMat 266) (codeMat 249) (codeMat 425) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit31_lb15

theorem plane452GenSource0089 :
    QuotientRankAtLeast (spanCodes [257, 32, 16, 9, 4, 3]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68] [(257, 112), (32, 1), (16, 2), (9, 54), (4, 8), (3, 32)]
    (codeMat 266) (codeMat 92) (codeMat 116) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit31_lb15

end QiushiMatmul
