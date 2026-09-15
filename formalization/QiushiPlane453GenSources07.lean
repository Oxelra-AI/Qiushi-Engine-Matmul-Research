import QiushiPlane453GenData
import QiushiCertifiedTransport
import QiushiMonoOrbit198From77T
import QiushiOrbit31FP
import QiushiStep128Mono189From80T
import QiushiWcOrbit128Dispatch
import QiushiWcOrbit187Dispatch
import QiushiWcOrbit197Dispatch
import QiushiWcOrbit220Dispatch
import QiushiWcOrbit72Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane453GenSource0070 :
    QuotientRankAtLeast (spanCodes [132, 68, 20, 8, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68] [(132, 82), (68, 80), (20, 100), (8, 32), (2, 9), (1, 8)]
    (codeMat 161) (codeMat 282) (codeMat 267) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit31_lb15

theorem plane453GenSource0071 :
    QuotientRankAtLeast (spanCodes [134, 68, 36, 20, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [326, 132, 32, 10, 1] [(134, 332), (68, 483), (36, 32), (20, 33), (10, 42)]
    (codeMat 410) (codeMat 459) (codeMat 346) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit198_lb15_mono

theorem plane453GenSource0072 :
    QuotientRankAtLeast (spanCodes [162, 66, 18, 10, 6]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [324, 132, 32, 10, 1] [(162, 367), (66, 356), (18, 325), (10, 324), (6, 448)]
    (codeMat 114) (codeMat 226) (codeMat 141) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit197_lb15_wc

theorem plane453GenSource0073 :
    QuotientRankAtLeast (spanCodes [163, 66, 18, 10, 6]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [324, 132, 32, 10, 1] [(163, 143), (66, 356), (18, 1), (10, 324), (6, 448)]
    (codeMat 115) (codeMat 354) (codeMat 142) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit197_lb15_wc

theorem plane453GenSource0074 :
    QuotientRankAtLeast (spanCodes [130, 68, 36, 20, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 32, 10, 1] [(130, 128), (68, 429), (36, 390), (20, 422), (10, 138)]
    (codeMat 342) (codeMat 313) (codeMat 313) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit187_lb15_wc

theorem plane453GenSource0075 :
    QuotientRankAtLeast (spanCodes [259, 66, 18, 10, 6]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [334, 192, 36, 16, 1] [(259, 378), (66, 209), (18, 1), (10, 17), (6, 36)]
    (codeMat 403) (codeMat 271) (codeMat 314) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit220_lb15_wc

theorem plane453GenSource0076 :
    QuotientRankAtLeast (spanCodes [260, 68, 32, 20, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [384, 96, 12, 2, 1] [(260, 2), (68, 386), (32, 1), (20, 12), (10, 97)]
    (codeMat 106) (codeMat 85) (codeMat 340) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit128_lb15_wc

theorem plane453GenSource0077 :
    QuotientRankAtLeast (spanCodes [292, 68, 20, 8, 2]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 32, 10, 1] [(292, 128), (68, 294), (20, 10), (8, 32), (2, 1)]
    (codeMat 465) (codeMat 98) (codeMat 140) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit187_lb15_wc

theorem plane453GenSource0078 :
    QuotientRankAtLeast (spanCodes [257, 128, 68, 20, 9, 3]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 68, 32, 20, 10, 1] [(257, 42), (128, 1), (68, 21), (20, 81), (9, 365), (3, 32)]
    (codeMat 396) (codeMat 99) (codeMat 172) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit72_lb15_wc

theorem plane453GenSource0079 :
    QuotientRankAtLeast (spanCodes [385, 65, 17, 10, 5]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 128, 32, 10, 1] [(385, 406), (65, 32), (17, 11), (10, 10), (5, 128)]
    (codeMat 331) (codeMat 314) (codeMat 271) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit189_lb15_mono

end QiushiMatmul
