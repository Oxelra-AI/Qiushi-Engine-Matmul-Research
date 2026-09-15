import QiushiPlane459GenData
import QiushiCertifiedTransport
import QiushiOrbit29FP
import QiushiStep132Mono385From243
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane459GenSource0030 :
    QuotientRankAtLeast (spanCodes [295, 160, 68, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [160, 68, 20, 10] [(295, 180), (160, 170), (68, 10), (10, 228)]
    (codeMat 229) (codeMat 187) (codeMat 229) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit385_lb17_mono

theorem plane459GenSource0031 :
    QuotientRankAtLeast (spanCodes [305, 160, 68, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [160, 68, 20, 10] [(305, 250), (160, 68), (68, 170), (10, 228)]
    (codeMat 174) (codeMat 461) (codeMat 234) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit385_lb17_mono

theorem plane459GenSource0032 :
    QuotientRankAtLeast (spanCodes [306, 160, 68, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [160, 68, 20, 10] [(306, 180), (160, 160), (68, 170), (10, 228)]
    (codeMat 167) (codeMat 233) (codeMat 233) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit385_lb17_mono

theorem plane459GenSource0033 :
    QuotientRankAtLeast (spanCodes [308, 160, 68, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [160, 68, 20, 10] [(308, 30), (160, 238), (68, 170), (10, 228)]
    (codeMat 239) (codeMat 351) (codeMat 239) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit385_lb17_mono

theorem plane459GenSource0034 :
    QuotientRankAtLeast (spanCodes [310, 160, 68, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [160, 68, 20, 10] [(310, 80), (160, 10), (68, 170), (10, 228)]
    (codeMat 230) (codeMat 123) (codeMat 236) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit385_lb17_mono

theorem plane459GenSource0035 :
    QuotientRankAtLeast (spanCodes [160, 68, 16, 8, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160] [(160, 68), (68, 160), (16, 1), (8, 2), (2, 8), (1, 16)]
    (codeMat 266) (codeMat 266) (codeMat 266) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit29_lb15

theorem plane459GenSource0036 :
    QuotientRankAtLeast (spanCodes [256, 160, 64, 10, 4, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160] [(256, 1), (160, 68), (64, 2), (10, 160), (4, 8), (1, 16)]
    (codeMat 140) (codeMat 140) (codeMat 98) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit29_lb15

theorem plane459GenSource0037 :
    QuotientRankAtLeast (spanCodes [272, 160, 66, 10, 6, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160] [(272, 68), (160, 69), (66, 170), (10, 168), (6, 8), (1, 16)]
    (codeMat 142) (codeMat 394) (codeMat 330) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit29_lb15

theorem plane459GenSource0038 :
    QuotientRankAtLeast (spanCodes [256, 128, 68, 32, 16, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160] [(256, 1), (128, 2), (68, 68), (32, 8), (16, 16), (10, 160)]
    (codeMat 84) (codeMat 84) (codeMat 84) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit29_lb15

theorem plane459GenSource0039 :
    QuotientRankAtLeast (spanCodes [257, 130, 68, 34, 16, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160] [(257, 68), (130, 2), (68, 69), (34, 160), (16, 16), (10, 168)]
    (codeMat 85) (codeMat 337) (codeMat 337) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit29_lb15

end QiushiMatmul
