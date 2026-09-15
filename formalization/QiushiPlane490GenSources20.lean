import QiushiPlane490GenData
import QiushiCertifiedTransport
import QiushiMonoOrbit103From35T
import QiushiOrbit101FP
import QiushiOrbit35FP
import QiushiStep99Orbit144Dispatch
import QiushiWcOrbit157Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane490GenSource0200 :
    QuotientRankAtLeast (spanCodes [256, 35, 19, 10, 5]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [128, 32, 20, 10, 1] [(256, 128), (35, 42), (19, 43), (10, 30), (5, 32)]
    (codeMat 266) (codeMat 122) (codeMat 460) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit157_lb15_wc

theorem plane490GenSource0201 :
    QuotientRankAtLeast (spanCodes [257, 32, 18, 10, 7]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [132, 32, 8, 2, 1] [(257, 173), (32, 2), (18, 32), (10, 35), (7, 9)]
    (codeMat 346) (codeMat 233) (codeMat 233) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit103_lb15_mono

theorem plane490GenSource0202 :
    QuotientRankAtLeast (spanCodes [257, 34, 18, 10, 6]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [132, 32, 8, 2, 1] [(257, 164), (34, 11), (18, 3), (10, 43), (6, 9)]
    (codeMat 339) (codeMat 122) (codeMat 460) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit103_lb15_mono

theorem plane490GenSource0203 :
    QuotientRankAtLeast (spanCodes [257, 32, 18, 10, 4]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 32, 84] [(257, 118), (32, 8), (18, 2), (10, 34), (4, 9)]
    (codeMat 275) (codeMat 92) (codeMat 116) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit101_lb15

theorem plane490GenSource0204 :
    QuotientRankAtLeast (spanCodes [273, 48, 8, 4, 2]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [132, 32, 8, 2, 1] [(273, 140), (48, 8), (8, 32), (4, 2), (2, 3)]
    (codeMat 401) (codeMat 114) (codeMat 204) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit103_lb15_mono

theorem plane490GenSource0205 :
    QuotientRankAtLeast (spanCodes [272, 49, 9, 4, 3]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [132, 32, 8, 2, 1] [(272, 164), (49, 33), (9, 40), (4, 2), (3, 3)]
    (codeMat 409) (codeMat 241) (codeMat 489) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit103_lb15_mono

theorem plane490GenSource0206 :
    QuotientRankAtLeast (spanCodes [257, 64, 16, 8, 2]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [132, 32, 8, 2, 1] [(257, 132), (64, 2), (16, 8), (8, 1), (2, 32)]
    (codeMat 98) (codeMat 273) (codeMat 273) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit103_lb15_mono

theorem plane490GenSource0207 :
    QuotientRankAtLeast (spanCodes [275, 83, 51, 10, 4]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [408, 84, 32, 2, 1] [(275, 461), (83, 493), (51, 463), (10, 118), (4, 1)]
    (codeMat 305) (codeMat 141) (codeMat 226) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit144_lb15_unconditional

theorem plane490GenSource0208 :
    QuotientRankAtLeast (spanCodes [274, 64, 32, 10, 4, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(274, 118), (64, 128), (32, 8), (10, 22), (4, 1), (1, 2)]
    (codeMat 273) (codeMat 156) (codeMat 102) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane490GenSource0209 :
    QuotientRankAtLeast (spanCodes [274, 66, 34, 10, 4, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(274, 252), (66, 148), (34, 28), (10, 20), (4, 3), (1, 2)]
    (codeMat 401) (codeMat 172) (codeMat 99) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

end QiushiMatmul
