import QiushiPlane426GenData
import QiushiCertifiedTransport
import QiushiMonoOrbit103From35T
import QiushiMonoOrbit112From35T
import QiushiOrbit35FP
import QiushiWcOrbit141Dispatch
import QiushiWcOrbit185Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane426GenSource0080 :
    QuotientRankAtLeast (spanCodes [272, 86, 48, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [400, 84, 32, 10, 1] [(272, 400), (86, 84), (48, 32), (10, 10), (1, 1)]
    (codeMat 273) (codeMat 305) (codeMat 305) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit185_lb15_wc

theorem plane426GenSource0081 :
    QuotientRankAtLeast (spanCodes [272, 64, 34, 10, 4, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(272, 224), (64, 128), (34, 28), (10, 20), (4, 3), (1, 2)]
    (codeMat 273) (codeMat 172) (codeMat 99) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane426GenSource0082 :
    QuotientRankAtLeast (spanCodes [272, 66, 32, 10, 4, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(272, 104), (66, 148), (32, 8), (10, 20), (4, 1), (1, 2)]
    (codeMat 401) (codeMat 140) (codeMat 98) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane426GenSource0083 :
    QuotientRankAtLeast (spanCodes [272, 100, 8, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 96, 8, 2, 1] [(272, 274), (100, 96), (8, 9), (2, 2), (1, 1)]
    (codeMat 281) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit112_lb15_mono

theorem plane426GenSource0084 :
    QuotientRankAtLeast (spanCodes [272, 68, 32, 8, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(272, 96), (68, 20), (32, 8), (8, 1), (2, 128), (1, 2)]
    (codeMat 266) (codeMat 161) (codeMat 161) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane426GenSource0085 :
    QuotientRankAtLeast (spanCodes [272, 84, 38, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [264, 84, 32, 2, 1] [(272, 350), (84, 380), (38, 297), (10, 264), (1, 32)]
    (codeMat 107) (codeMat 188) (codeMat 103) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit141_lb15_wc

theorem plane426GenSource0086 :
    QuotientRankAtLeast (spanCodes [272, 80, 32, 10, 4, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(272, 96), (80, 224), (32, 8), (10, 28), (4, 1), (1, 3)]
    (codeMat 273) (codeMat 141) (codeMat 226) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane426GenSource0087 :
    QuotientRankAtLeast (spanCodes [272, 84, 34, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [264, 84, 32, 2, 1] [(272, 118), (84, 84), (34, 265), (10, 264), (1, 32)]
    (codeMat 106) (codeMat 172) (codeMat 99) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit141_lb15_wc

theorem plane426GenSource0088 :
    QuotientRankAtLeast (spanCodes [272, 82, 32, 10, 4, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(272, 104), (82, 252), (32, 8), (10, 28), (4, 1), (1, 3)]
    (codeMat 401) (codeMat 141) (codeMat 226) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane426GenSource0089 :
    QuotientRankAtLeast (spanCodes [272, 128, 8, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [132, 32, 8, 2, 1] [(272, 132), (128, 2), (8, 32), (2, 1), (1, 8)]
    (codeMat 161) (codeMat 266) (codeMat 266) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit103_lb15_mono

end QiushiMatmul
