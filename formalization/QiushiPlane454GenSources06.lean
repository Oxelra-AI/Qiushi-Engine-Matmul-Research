import QiushiPlane454GenData
import QiushiCertifiedTransport
import QiushiOrbit31FP
import QiushiOrbit35FP
import QiushiWcOrbit128Dispatch
import QiushiWcOrbit157Dispatch
import QiushiWcOrbit187Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane454GenSource0060 :
    QuotientRankAtLeast (spanCodes [67, 35, 17, 10, 5]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [128, 32, 20, 10, 1] [(67, 170), (35, 62), (17, 21), (10, 42), (5, 32)]
    (codeMat 458) (codeMat 426) (codeMat 335) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit157_lb15_wc

theorem plane454GenSource0061 :
    QuotientRankAtLeast (spanCodes [68, 36, 20, 8, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68] [(68, 112), (36, 54), (20, 52), (8, 1), (2, 32), (1, 8)]
    (codeMat 266) (codeMat 417) (codeMat 177) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit31_lb15

theorem plane454GenSource0062 :
    QuotientRankAtLeast (spanCodes [128, 96, 20, 8, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(128, 128), (96, 96), (20, 20), (8, 8), (2, 2), (1, 1)]
    (codeMat 273) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane454GenSource0063 :
    QuotientRankAtLeast (spanCodes [130, 96, 16, 10, 4]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [384, 96, 12, 2, 1] [(130, 2), (96, 96), (16, 1), (10, 14), (4, 384)]
    (codeMat 298) (codeMat 266) (codeMat 266) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit128_lb15_wc

theorem plane454GenSource0064 :
    QuotientRankAtLeast (spanCodes [129, 96, 16, 8, 4, 2]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(129, 20), (96, 96), (16, 1), (8, 8), (4, 128), (2, 2)]
    (codeMat 266) (codeMat 266) (codeMat 266) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane454GenSource0065 :
    QuotientRankAtLeast (spanCodes [132, 96, 20, 8, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(132, 148), (96, 104), (20, 20), (8, 8), (2, 2), (1, 1)]
    (codeMat 401) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane454GenSource0066 :
    QuotientRankAtLeast (spanCodes [130, 68, 36, 20, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 32, 10, 1] [(130, 128), (68, 429), (36, 390), (20, 422), (10, 138)]
    (codeMat 342) (codeMat 313) (codeMat 313) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit187_lb15_wc

theorem plane454GenSource0067 :
    QuotientRankAtLeast (spanCodes [161, 96, 17, 9, 5, 3]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(161, 234), (96, 252), (17, 10), (9, 9), (5, 130), (3, 2)]
    (codeMat 267) (codeMat 313) (codeMat 313) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane454GenSource0068 :
    QuotientRankAtLeast (spanCodes [164, 96, 20, 8, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(164, 252), (96, 104), (20, 28), (8, 8), (2, 3), (1, 1)]
    (codeMat 401) (codeMat 275) (codeMat 275) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane454GenSource0069 :
    QuotientRankAtLeast (spanCodes [256, 128, 96, 16, 10, 4]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(256, 2), (128, 1), (96, 20), (16, 8), (10, 96), (4, 128)]
    (codeMat 84) (codeMat 98) (codeMat 140) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

end QiushiMatmul
