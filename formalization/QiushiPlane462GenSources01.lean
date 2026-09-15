import QiushiPlane462GenData
import QiushiCertifiedTransport
import QiushiOrbit29FP
import QiushiWcOrbit187Dispatch
import QiushiWcOrbit75Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane462GenSource0010 :
    QuotientRankAtLeast (spanCodes [262, 129, 68, 38, 21, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 160, 68, 20, 10, 1] [(262, 329), (129, 228), (68, 91), (38, 328), (21, 160), (10, 280)]
    (codeMat 86) (codeMat 141) (codeMat 226) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit75_lb16_wc

theorem plane462GenSource0011 :
    QuotientRankAtLeast (spanCodes [257, 134, 68, 35, 23, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 160, 68, 20, 10, 1] [(257, 68), (134, 263), (68, 69), (35, 160), (23, 440), (10, 488)]
    (codeMat 85) (codeMat 467) (codeMat 339) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit75_lb16_wc

theorem plane462GenSource0012 :
    QuotientRankAtLeast (spanCodes [262, 129, 68, 37, 22, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 160, 68, 20, 10, 1] [(262, 191), (129, 429), (68, 502), (37, 440), (22, 488), (10, 240)]
    (codeMat 95) (codeMat 494) (codeMat 501) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit75_lb16_wc

theorem plane462GenSource0013 :
    QuotientRankAtLeast (spanCodes [263, 131, 68, 38, 23, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 160, 68, 20, 10, 1] [(263, 69), (131, 263), (68, 323), (38, 488), (23, 440), (10, 280)]
    (codeMat 92) (codeMat 415) (codeMat 253) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit75_lb16_wc

theorem plane462GenSource0014 :
    QuotientRankAtLeast (spanCodes [160, 68, 16, 8, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160] [(160, 68), (68, 160), (16, 1), (8, 2), (2, 8), (1, 16)]
    (codeMat 266) (codeMat 266) (codeMat 266) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit29_lb15

theorem plane462GenSource0015 :
    QuotientRankAtLeast (spanCodes [145, 67, 35, 10, 7]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 32, 10, 1] [(145, 129), (67, 139), (35, 422), (10, 138), (7, 390)]
    (codeMat 415) (codeMat 275) (codeMat 275) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit187_lb15_wc

theorem plane462GenSource0016 :
    QuotientRankAtLeast (spanCodes [146, 65, 32, 10, 5]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 32, 10, 1] [(146, 1), (65, 128), (32, 390), (10, 138), (5, 32)]
    (codeMat 335) (codeMat 298) (codeMat 270) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit187_lb15_wc

theorem plane462GenSource0017 :
    QuotientRankAtLeast (spanCodes [144, 67, 34, 10, 7]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 32, 10, 1] [(144, 128), (67, 139), (34, 170), (10, 138), (7, 390)]
    (codeMat 407) (codeMat 277) (codeMat 277) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit187_lb15_wc

theorem plane462GenSource0018 :
    QuotientRankAtLeast (spanCodes [146, 66, 32, 10, 6]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 32, 10, 1] [(146, 128), (66, 139), (32, 32), (10, 138), (6, 390)]
    (codeMat 470) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit187_lb15_wc

theorem plane462GenSource0019 :
    QuotientRankAtLeast (spanCodes [144, 64, 34, 10, 4]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 32, 10, 1] [(144, 1), (64, 128), (34, 268), (10, 138), (4, 32)]
    (codeMat 270) (codeMat 266) (codeMat 266) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit187_lb15_wc

end QiushiMatmul
