import QiushiPlane426GenData
import QiushiCertifiedTransport
import QiushiMonoOrbit112From35T
import QiushiOrbit31FP
import QiushiOrbit35FP
import QiushiStep128Mono158From72
import QiushiWcOrbit183Dispatch
import QiushiWcOrbit185Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane426GenSource0070 :
    QuotientRankAtLeast (spanCodes [260, 38, 20, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [192, 32, 20, 10, 1] [(260, 192), (38, 43), (20, 30), (10, 52), (1, 32)]
    (codeMat 330) (codeMat 244) (codeMat 95) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit158_lb15_mono

theorem plane426GenSource0071 :
    QuotientRankAtLeast (spanCodes [258, 32, 18, 10, 4, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68] [(258, 112), (32, 1), (18, 54), (10, 52), (4, 8), (1, 32)]
    (codeMat 266) (codeMat 212) (codeMat 86) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit31_lb15

theorem plane426GenSource0072 :
    QuotientRankAtLeast (spanCodes [260, 64, 20, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 96, 8, 2, 1] [(260, 2), (64, 9), (20, 272), (10, 96), (1, 8)]
    (codeMat 141) (codeMat 161) (codeMat 161) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit112_lb15_mono

theorem plane426GenSource0073 :
    QuotientRankAtLeast (spanCodes [272, 80, 10, 4, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 96, 8, 2, 1] [(272, 274), (80, 272), (10, 96), (4, 9), (1, 8)]
    (codeMat 161) (codeMat 172) (codeMat 99) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit112_lb15_mono

theorem plane426GenSource0074 :
    QuotientRankAtLeast (spanCodes [272, 84, 52, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [384, 84, 32, 10, 1] [(272, 469), (84, 84), (52, 42), (10, 11), (1, 1)]
    (codeMat 345) (codeMat 309) (codeMat 309) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit183_lb15_wc

theorem plane426GenSource0075 :
    QuotientRankAtLeast (spanCodes [272, 86, 52, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [400, 84, 32, 10, 1] [(272, 411), (86, 94), (52, 43), (10, 10), (1, 1)]
    (codeMat 281) (codeMat 307) (codeMat 311) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit185_lb15_wc

theorem plane426GenSource0076 :
    QuotientRankAtLeast (spanCodes [272, 68, 36, 8, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(272, 224), (68, 20), (36, 8), (8, 3), (2, 128), (1, 2)]
    (codeMat 267) (codeMat 161) (codeMat 161) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane426GenSource0077 :
    QuotientRankAtLeast (spanCodes [272, 84, 48, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [384, 84, 32, 10, 1] [(272, 479), (84, 94), (48, 32), (10, 11), (1, 1)]
    (codeMat 337) (codeMat 311) (codeMat 307) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit183_lb15_wc

theorem plane426GenSource0078 :
    QuotientRankAtLeast (spanCodes [272, 64, 32, 10, 4, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(272, 96), (64, 128), (32, 8), (10, 20), (4, 1), (1, 2)]
    (codeMat 273) (codeMat 140) (codeMat 98) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane426GenSource0079 :
    QuotientRankAtLeast (spanCodes [272, 66, 34, 10, 4, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(272, 232), (66, 150), (34, 30), (10, 22), (4, 3), (1, 2)]
    (codeMat 401) (codeMat 188) (codeMat 103) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

end QiushiMatmul
