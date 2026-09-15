import QiushiPlane489GenData
import QiushiCertifiedTransport
import QiushiMonoOrbit103From35T
import QiushiMonoOrbit112From35T
import QiushiOrbit35FP
import QiushiWcOrbit157Dispatch
import QiushiWcOrbit187Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane489GenSource0170 :
    QuotientRankAtLeast (spanCodes [258, 129, 83, 51, 10, 5]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(258, 118), (129, 255), (83, 28), (51, 136), (10, 224), (5, 128)]
    (codeMat 94) (codeMat 498) (codeMat 206) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane489GenSource0171 :
    QuotientRankAtLeast (spanCodes [257, 145, 64, 52, 9, 3]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(257, 118), (145, 131), (64, 9), (52, 232), (9, 8), (3, 128)]
    (codeMat 95) (codeMat 307) (codeMat 311) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane489GenSource0172 :
    QuotientRankAtLeast (spanCodes [257, 208, 49, 9, 4, 3]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(257, 97), (208, 252), (49, 129), (9, 130), (4, 8), (3, 9)]
    (codeMat 281) (codeMat 241) (codeMat 489) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane489GenSource0173 :
    QuotientRankAtLeast (spanCodes [258, 144, 83, 36, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 32, 10, 1] [(258, 294), (144, 128), (83, 129), (36, 390), (10, 139)]
    (codeMat 445) (codeMat 313) (codeMat 313) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit187_lb15_wc

theorem plane489GenSource0174 :
    QuotientRankAtLeast (spanCodes [258, 144, 65, 54, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 32, 10, 1] [(258, 139), (144, 128), (65, 390), (54, 1), (10, 294)]
    (codeMat 443) (codeMat 124) (codeMat 124) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit187_lb15_wc

theorem plane489GenSource0175 :
    QuotientRankAtLeast (spanCodes [258, 146, 83, 32, 10, 6]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(258, 137), (146, 3), (83, 252), (32, 8), (10, 224), (6, 128)]
    (codeMat 87) (codeMat 86) (codeMat 212) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane489GenSource0176 :
    QuotientRankAtLeast (spanCodes [258, 210, 48, 10, 5]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 32, 10, 1] [(258, 429), (210, 295), (48, 390), (10, 263), (5, 128)]
    (codeMat 115) (codeMat 351) (codeMat 239) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit187_lb15_wc

theorem plane489GenSource0177 :
    QuotientRankAtLeast (spanCodes [258, 146, 82, 48, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [128, 32, 20, 10, 1] [(258, 148), (146, 128), (82, 129), (48, 32), (10, 138)]
    (codeMat 468) (codeMat 313) (codeMat 313) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit157_lb15_wc

theorem plane489GenSource0178 :
    QuotientRankAtLeast (spanCodes [258, 128, 66, 50, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [132, 32, 8, 2, 1] [(258, 134), (128, 2), (66, 133), (50, 164), (10, 173)]
    (codeMat 116) (codeMat 369) (codeMat 377) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit103_lb15_mono

theorem plane489GenSource0179 :
    QuotientRankAtLeast (spanCodes [258, 144, 85, 53, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 96, 8, 2, 1] [(258, 371), (144, 9), (85, 377), (53, 272), (10, 274)]
    (codeMat 158) (codeMat 351) (codeMat 239) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit112_lb15_mono

end QiushiMatmul
