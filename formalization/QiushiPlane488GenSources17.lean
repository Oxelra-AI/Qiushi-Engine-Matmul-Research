import QiushiPlane488GenData
import QiushiCertifiedTransport
import QiushiMonoOrbit103From35T
import QiushiMonoOrbit192From65
import QiushiOrbit101FP
import QiushiOrbit31FP
import QiushiOrbit35FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane488GenSource0170 :
    QuotientRankAtLeast (spanCodes [128, 65, 33, 8, 2]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [132, 32, 8, 2, 1] [(128, 40), (65, 1), (33, 132), (8, 2), (2, 32)]
    (codeMat 85) (codeMat 273) (codeMat 273) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit103_lb15_mono

theorem plane488GenSource0171 :
    QuotientRankAtLeast (spanCodes [160, 96, 8, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [132, 32, 8, 2, 1] [(160, 164), (96, 132), (8, 2), (2, 9), (1, 1)]
    (codeMat 273) (codeMat 275) (codeMat 275) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit103_lb15_mono

theorem plane488GenSource0172 :
    QuotientRankAtLeast (spanCodes [146, 81, 49, 10, 7]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [340, 128, 32, 10, 1] [(146, 511), (81, 383), (49, 33), (10, 42), (7, 1)]
    (codeMat 345) (codeMat 247) (codeMat 379) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit192_lb15_mono

theorem plane488GenSource0173 :
    QuotientRankAtLeast (spanCodes [130, 65, 33, 18, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [132, 32, 8, 2, 1] [(130, 8), (65, 9), (33, 166), (18, 32), (10, 34)]
    (codeMat 213) (codeMat 313) (codeMat 313) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit103_lb15_mono

theorem plane488GenSource0174 :
    QuotientRankAtLeast (spanCodes [128, 67, 35, 18, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [132, 32, 8, 2, 1] [(128, 40), (67, 43), (35, 134), (18, 32), (10, 34)]
    (codeMat 215) (codeMat 281) (codeMat 281) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit103_lb15_mono

theorem plane488GenSource0175 :
    QuotientRankAtLeast (spanCodes [129, 65, 33, 16, 8, 2]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68] [(129, 52), (65, 54), (33, 100), (16, 8), (8, 9), (2, 32)]
    (codeMat 98) (codeMat 281) (codeMat 281) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit31_lb15

theorem plane488GenSource0176 :
    QuotientRankAtLeast (spanCodes [144, 65, 33, 8, 2]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [132, 32, 8, 2, 1] [(144, 40), (65, 3), (33, 132), (8, 2), (2, 32)]
    (codeMat 87) (codeMat 273) (codeMat 273) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit103_lb15_mono

theorem plane488GenSource0177 :
    QuotientRankAtLeast (spanCodes [161, 96, 16, 8, 2]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 32, 84] [(161, 84), (96, 118), (16, 8), (8, 9), (2, 32)]
    (codeMat 106) (codeMat 281) (codeMat 281) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit101_lb15

theorem plane488GenSource0178 :
    QuotientRankAtLeast (spanCodes [176, 96, 8, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [132, 32, 8, 2, 1] [(176, 164), (96, 134), (8, 2), (2, 9), (1, 1)]
    (codeMat 401) (codeMat 275) (codeMat 275) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit103_lb15_mono

theorem plane488GenSource0179 :
    QuotientRankAtLeast (spanCodes [164, 96, 20, 8, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(164, 252), (96, 104), (20, 28), (8, 8), (2, 3), (1, 1)]
    (codeMat 401) (codeMat 275) (codeMat 275) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

end QiushiMatmul
