import QiushiPlane453GenData
import QiushiCertifiedTransport
import QiushiOrbit31FP
import QiushiWcOrbit157Dispatch
import QiushiWcOrbit194Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane453GenSource0060 :
    QuotientRankAtLeast (spanCodes [288, 134, 68, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 132, 32, 10, 1] [(288, 1), (134, 301), (68, 393), (20, 269), (10, 418)]
    (codeMat 318) (codeMat 204) (codeMat 114) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit194_lb16_wc

theorem plane453GenSource0061 :
    QuotientRankAtLeast (spanCodes [384, 68, 38, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 132, 32, 10, 1] [(384, 32), (68, 424), (38, 262), (20, 386), (10, 133)]
    (codeMat 98) (codeMat 369) (codeMat 377) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit194_lb16_wc

theorem plane453GenSource0062 :
    QuotientRankAtLeast (spanCodes [417, 67, 19, 10, 7]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 132, 32, 10, 1] [(417, 425), (67, 294), (19, 386), (10, 262), (7, 1)]
    (codeMat 185) (codeMat 244) (codeMat 95) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit194_lb16_wc

theorem plane453GenSource0063 :
    QuotientRankAtLeast (spanCodes [294, 129, 68, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 132, 32, 10, 1] [(294, 42), (129, 164), (68, 393), (20, 175), (10, 418)]
    (codeMat 382) (codeMat 380) (codeMat 117) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit194_lb16_wc

theorem plane453GenSource0064 :
    QuotientRankAtLeast (spanCodes [390, 68, 33, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 132, 32, 10, 1] [(390, 32), (68, 424), (33, 387), (20, 263), (10, 133)]
    (codeMat 107) (codeMat 247) (codeMat 379) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit194_lb16_wc

theorem plane453GenSource0065 :
    QuotientRankAtLeast (spanCodes [416, 67, 19, 10, 7]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 132, 32, 10, 1] [(416, 175), (67, 294), (19, 132), (10, 262), (7, 1)]
    (codeMat 249) (codeMat 372) (codeMat 93) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit194_lb16_wc

theorem plane453GenSource0066 :
    QuotientRankAtLeast (spanCodes [68, 32, 20, 8, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68] [(68, 80), (32, 2), (20, 20), (8, 1), (2, 32), (1, 8)]
    (codeMat 266) (codeMat 161) (codeMat 161) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit31_lb15

theorem plane453GenSource0067 :
    QuotientRankAtLeast (spanCodes [68, 36, 20, 8, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68] [(68, 112), (36, 54), (20, 52), (8, 1), (2, 32), (1, 8)]
    (codeMat 266) (codeMat 417) (codeMat 177) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit31_lb15

theorem plane453GenSource0068 :
    QuotientRankAtLeast (spanCodes [128, 68, 20, 8, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68] [(128, 2), (68, 80), (20, 68), (8, 32), (2, 1), (1, 8)]
    (codeMat 161) (codeMat 266) (codeMat 266) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit31_lb15

theorem plane453GenSource0069 :
    QuotientRankAtLeast (spanCodes [131, 65, 17, 10, 5]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [128, 32, 20, 10, 1] [(131, 11), (65, 1), (17, 52), (10, 20), (5, 128)]
    (codeMat 205) (codeMat 279) (codeMat 279) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit157_lb15_wc

end QiushiMatmul
