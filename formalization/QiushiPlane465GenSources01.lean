import QiushiPlane465GenData
import QiushiCertifiedTransport
import QiushiWcOrbit213Dispatch
import QiushiWcOrbit214Dispatch
import QiushiWcOrbit218Dispatch
import QiushiWcOrbit238Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane465GenSource0010 :
    QuotientRankAtLeast (spanCodes [262, 151, 68, 54, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [310, 132, 96, 10, 1] [(262, 97), (151, 238), (68, 316), (54, 1), (10, 133)]
    (codeMat 163) (codeMat 459) (codeMat 346) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit218_lb16_wc

theorem plane465GenSource0011 :
    QuotientRankAtLeast (spanCodes [275, 128, 68, 35, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 132, 96, 10, 1] [(275, 107), (128, 504), (68, 238), (35, 402), (10, 228)]
    (codeMat 254) (codeMat 443) (codeMat 254) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit214_lb16_wc

theorem plane465GenSource0012 :
    QuotientRankAtLeast (spanCodes [274, 129, 68, 34, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 132, 96, 10, 1] [(274, 97), (129, 374), (68, 238), (34, 284), (10, 228)]
    (codeMat 247) (codeMat 415) (codeMat 253) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit214_lb16_wc

theorem plane465GenSource0013 :
    QuotientRankAtLeast (spanCodes [273, 130, 68, 33, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [276, 132, 96, 10, 1] [(273, 106), (130, 1), (68, 96), (33, 400), (10, 132)]
    (codeMat 85) (codeMat 354) (codeMat 142) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit213_lb16_wc

theorem plane465GenSource0014 :
    QuotientRankAtLeast (spanCodes [258, 145, 68, 50, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [276, 132, 96, 10, 1] [(258, 383), (145, 400), (68, 228), (50, 133), (10, 132)]
    (codeMat 122) (codeMat 372) (codeMat 93) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit213_lb16_wc

theorem plane465GenSource0015 :
    QuotientRankAtLeast (spanCodes [257, 146, 68, 49, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 132, 96, 10, 1] [(257, 11), (146, 504), (68, 10), (49, 374), (10, 228)]
    (codeMat 229) (codeMat 187) (codeMat 229) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit214_lb16_wc

theorem plane465GenSource0016 :
    QuotientRankAtLeast (spanCodes [256, 147, 68, 48, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 132, 96, 10, 1] [(256, 1), (147, 374), (68, 10), (48, 504), (10, 228)]
    (codeMat 236) (codeMat 159) (codeMat 230) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit214_lb16_wc

theorem plane465GenSource0017 :
    QuotientRankAtLeast (spanCodes [295, 164, 68, 23, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [294, 136, 96, 20, 1] [(295, 20), (164, 475), (68, 462), (23, 326), (10, 232)]
    (codeMat 501) (codeMat 236) (codeMat 123) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit238_lb16_wc

theorem plane465GenSource0018 :
    QuotientRankAtLeast (spanCodes [293, 161, 68, 21, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [294, 136, 96, 20, 1] [(293, 475), (161, 253), (68, 295), (21, 463), (10, 430)]
    (codeMat 468) (codeMat 409) (codeMat 473) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit238_lb16_wc

theorem plane465GenSource0019 :
    QuotientRankAtLeast (spanCodes [295, 161, 68, 23, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [294, 136, 96, 20, 1] [(295, 252), (161, 253), (68, 137), (23, 232), (10, 430)]
    (codeMat 421) (codeMat 125) (codeMat 348) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit238_lb16_wc

end QiushiMatmul
