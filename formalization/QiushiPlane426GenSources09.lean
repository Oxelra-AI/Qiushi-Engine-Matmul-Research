import QiushiPlane426GenData
import QiushiCertifiedTransport
import QiushiMonoOrbit103From35T
import QiushiMonoOrbit192From65
import QiushiOrbit35FP
import QiushiStep128Mono158From72
import QiushiWcOrbit132Dispatch
import QiushiWcOrbit141Dispatch
import QiushiWcOrbit185Dispatch
import QiushiWcOrbit187Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane426GenSource0090 :
    QuotientRankAtLeast (spanCodes [272, 144, 50, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 32, 10, 1] [(272, 129), (144, 1), (50, 138), (10, 268), (1, 32)]
    (codeMat 270) (codeMat 102) (codeMat 156) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit187_lb15_wc

theorem plane426GenSource0091 :
    QuotientRankAtLeast (spanCodes [272, 146, 48, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 32, 10, 1] [(272, 422), (146, 128), (48, 32), (10, 10), (1, 1)]
    (codeMat 465) (codeMat 305) (codeMat 305) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit187_lb15_wc

theorem plane426GenSource0092 :
    QuotientRankAtLeast (spanCodes [272, 130, 52, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [340, 128, 32, 10, 1] [(272, 469), (130, 128), (52, 42), (10, 11), (1, 1)]
    (codeMat 345) (codeMat 309) (codeMat 309) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit192_lb15_mono

theorem plane426GenSource0093 :
    QuotientRankAtLeast (spanCodes [272, 144, 38, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [340, 128, 32, 10, 1] [(272, 383), (144, 128), (38, 42), (10, 11), (1, 1)]
    (codeMat 409) (codeMat 277) (codeMat 277) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit192_lb15_mono

theorem plane426GenSource0094 :
    QuotientRankAtLeast (spanCodes [272, 150, 32, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [400, 84, 32, 10, 1] [(272, 11), (150, 43), (32, 1), (10, 126), (1, 432)]
    (codeMat 354) (codeMat 94) (codeMat 500) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit185_lb15_wc

theorem plane426GenSource0095 :
    QuotientRankAtLeast (spanCodes [272, 176, 10, 6, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [304, 160, 12, 2, 1] [(272, 304), (176, 400), (10, 14), (6, 2), (1, 1)]
    (codeMat 273) (codeMat 401) (codeMat 401) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit132_lb15_wc

theorem plane426GenSource0096 :
    QuotientRankAtLeast (spanCodes [272, 146, 80, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [192, 32, 20, 10, 1] [(272, 222), (146, 1), (80, 30), (10, 52), (1, 32)]
    (codeMat 95) (codeMat 298) (codeMat 270) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit158_lb15_mono

theorem plane426GenSource0097 :
    QuotientRankAtLeast (spanCodes [272, 150, 84, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [264, 84, 32, 2, 1] [(272, 383), (150, 381), (84, 348), (10, 296), (1, 32)]
    (codeMat 141) (codeMat 486) (codeMat 157) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit141_lb15_wc

theorem plane426GenSource0098 :
    QuotientRankAtLeast (spanCodes [272, 192, 8, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [132, 32, 8, 2, 1] [(272, 164), (192, 2), (8, 32), (2, 9), (1, 8)]
    (codeMat 161) (codeMat 282) (codeMat 267) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit103_lb15_mono

theorem plane426GenSource0099 :
    QuotientRankAtLeast (spanCodes [272, 132, 68, 8, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(272, 224), (132, 28), (68, 20), (8, 128), (2, 3), (1, 2)]
    (codeMat 161) (codeMat 282) (codeMat 267) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

end QiushiMatmul
