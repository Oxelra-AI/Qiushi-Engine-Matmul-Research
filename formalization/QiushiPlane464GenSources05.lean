import QiushiPlane464GenData
import QiushiCertifiedTransport
import QiushiOrbit29FP
import QiushiWcOrbit187Dispatch
import QiushiWcOrbit201Dispatch
import QiushiWcOrbit214Dispatch
import QiushiWcOrbit238Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane464GenSource0050 :
    QuotientRankAtLeast (spanCodes [257, 128, 68, 52, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [340, 132, 32, 10, 1] [(257, 10), (128, 32), (68, 11), (52, 475), (10, 164)]
    (codeMat 165) (codeMat 172) (codeMat 99) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit201_lb16_wc

theorem plane464GenSource0051 :
    QuotientRankAtLeast (spanCodes [258, 131, 68, 55, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [340, 132, 32, 10, 1] [(258, 133), (131, 175), (68, 383), (55, 43), (10, 350)]
    (codeMat 431) (codeMat 395) (codeMat 474) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit201_lb16_wc

theorem plane464GenSource0052 :
    QuotientRankAtLeast (spanCodes [273, 144, 68, 36, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 132, 96, 10, 1] [(273, 106), (144, 504), (68, 132), (36, 1), (10, 96)]
    (codeMat 99) (codeMat 212) (codeMat 86) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit214_lb16_wc

theorem plane464GenSource0053 :
    QuotientRankAtLeast (spanCodes [277, 148, 68, 32, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [294, 136, 96, 20, 1] [(277, 117), (148, 137), (68, 462), (32, 1), (10, 21)]
    (codeMat 410) (codeMat 93) (codeMat 372) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit238_lb16_wc

theorem plane464GenSource0054 :
    QuotientRankAtLeast (spanCodes [276, 150, 68, 34, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [340, 132, 32, 10, 1] [(276, 506), (150, 341), (68, 497), (34, 133), (10, 132)]
    (codeMat 242) (codeMat 380) (codeMat 117) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit201_lb16_wc

theorem plane464GenSource0055 :
    QuotientRankAtLeast (spanCodes [276, 151, 68, 35, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [294, 136, 96, 20, 1] [(276, 136), (151, 327), (68, 462), (35, 295), (10, 475)]
    (codeMat 253) (codeMat 425) (codeMat 249) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit238_lb16_wc

theorem plane464GenSource0056 :
    QuotientRankAtLeast (spanCodes [295, 164, 68, 16, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 132, 96, 10, 1] [(295, 408), (164, 132), (68, 228), (16, 1), (10, 10)]
    (codeMat 282) (codeMat 267) (codeMat 282) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit214_lb16_wc

theorem plane464GenSource0057 :
    QuotientRankAtLeast (spanCodes [164, 68, 16, 8, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160] [(164, 228), (68, 160), (16, 3), (8, 2), (2, 24), (1, 16)]
    (codeMat 266) (codeMat 282) (codeMat 267) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit29_lb15

theorem plane464GenSource0058 :
    QuotientRankAtLeast (spanCodes [146, 66, 32, 10, 6]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 32, 10, 1] [(146, 128), (66, 139), (32, 32), (10, 138), (6, 390)]
    (codeMat 470) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit187_lb15_wc

theorem plane464GenSource0059 :
    QuotientRankAtLeast (spanCodes [147, 66, 33, 10, 6]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 32, 10, 1] [(147, 129), (66, 139), (33, 300), (10, 138), (6, 390)]
    (codeMat 478) (codeMat 279) (codeMat 279) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit187_lb15_wc

end QiushiMatmul
