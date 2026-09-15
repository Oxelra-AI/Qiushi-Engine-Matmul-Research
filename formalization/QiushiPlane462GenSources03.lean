import QiushiPlane462GenData
import QiushiCertifiedTransport
import QiushiWcOrbit187Dispatch
import QiushiWcOrbit72Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane462GenSource0030 :
    QuotientRankAtLeast (spanCodes [128, 66, 50, 10, 6]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 32, 10, 1] [(128, 1), (66, 10), (50, 268), (10, 138), (6, 32)]
    (codeMat 396) (codeMat 270) (codeMat 298) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit187_lb15_wc

theorem plane462GenSource0031 :
    QuotientRankAtLeast (spanCodes [129, 67, 33, 18, 10, 7]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 68, 32, 20, 10, 1] [(129, 101), (67, 332), (33, 53), (18, 1), (10, 33), (7, 63)]
    (codeMat 403) (codeMat 103) (codeMat 188) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit72_lb15_wc

theorem plane462GenSource0032 :
    QuotientRankAtLeast (spanCodes [135, 68, 32, 21, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 32, 10, 1] [(135, 301), (68, 429), (32, 390), (21, 300), (10, 138)]
    (codeMat 351) (codeMat 299) (codeMat 318) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit187_lb15_wc

theorem plane462GenSource0033 :
    QuotientRankAtLeast (spanCodes [135, 68, 34, 23, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 32, 10, 1] [(135, 294), (68, 295), (34, 170), (23, 422), (10, 138)]
    (codeMat 405) (codeMat 317) (codeMat 285) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit187_lb15_wc

theorem plane462GenSource0034 :
    QuotientRankAtLeast (spanCodes [131, 64, 49, 10, 4]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 32, 10, 1] [(131, 129), (64, 1), (49, 300), (10, 138), (4, 390)]
    (codeMat 348) (codeMat 307) (codeMat 311) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit187_lb15_wc

theorem plane462GenSource0035 :
    QuotientRankAtLeast (spanCodes [129, 66, 51, 10, 6]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 32, 10, 1] [(129, 11), (66, 10), (51, 300), (10, 138), (6, 32)]
    (codeMat 397) (codeMat 318) (codeMat 299) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit187_lb15_wc

theorem plane462GenSource0036 :
    QuotientRankAtLeast (spanCodes [132, 68, 34, 20, 10]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 32, 10, 1] [(132, 301), (68, 429), (34, 268), (20, 300), (10, 138)]
    (codeMat 286) (codeMat 271) (codeMat 314) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit187_lb15_wc

theorem plane462GenSource0037 :
    QuotientRankAtLeast (spanCodes [131, 67, 49, 10, 7]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 32, 10, 1] [(131, 11), (67, 10), (49, 422), (10, 138), (7, 32)]
    (codeMat 460) (codeMat 286) (codeMat 303) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit187_lb15_wc

theorem plane462GenSource0038 :
    QuotientRankAtLeast (spanCodes [132, 68, 33, 21, 8, 2]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 68, 32, 20, 10, 1] [(132, 316), (68, 81), (33, 11), (21, 20), (8, 1), (2, 32)]
    (codeMat 458) (codeMat 165) (codeMat 163) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit72_lb15_wc

theorem plane462GenSource0039 :
    QuotientRankAtLeast (spanCodes [130, 67, 48, 10, 7]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 32, 10, 1] [(130, 1), (67, 10), (48, 390), (10, 138), (7, 32)]
    (codeMat 461) (codeMat 302) (codeMat 302) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit187_lb15_wc

end QiushiMatmul
