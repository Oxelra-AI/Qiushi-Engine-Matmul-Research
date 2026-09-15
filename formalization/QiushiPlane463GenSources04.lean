import QiushiPlane463GenData
import QiushiCertifiedTransport
import QiushiWcOrbit164Dispatch
import QiushiWcOrbit214Dispatch
import QiushiWcOrbit236Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane463GenSource0040 :
    QuotientRankAtLeast (spanCodes [275, 131, 68, 48, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 132, 96, 10, 1] [(275, 409), (131, 402), (68, 228), (48, 1), (10, 132)]
    (codeMat 114) (codeMat 116) (codeMat 92) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit214_lb16_wc

theorem plane463GenSource0041 :
    QuotientRankAtLeast (spanCodes [262, 145, 68, 34, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 96, 20, 10, 1] [(262, 126), (145, 21), (68, 353), (34, 127), (10, 383)]
    (codeMat 183) (codeMat 215) (codeMat 342) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit164_lb16_wc

theorem plane463GenSource0042 :
    QuotientRankAtLeast (spanCodes [263, 144, 68, 35, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 96, 20, 10, 1] [(263, 363), (144, 256), (68, 30), (35, 362), (10, 383)]
    (codeMat 415) (codeMat 141) (codeMat 226) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit164_lb16_wc

theorem plane463GenSource0043 :
    QuotientRankAtLeast (spanCodes [272, 135, 68, 52, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 132, 96, 10, 1] [(272, 238), (135, 97), (68, 96), (52, 278), (10, 132)]
    (codeMat 93) (codeMat 482) (codeMat 143) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit214_lb16_wc

theorem plane463GenSource0044 :
    QuotientRankAtLeast (spanCodes [274, 133, 68, 54, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 132, 96, 10, 1] [(274, 505), (133, 374), (68, 228), (54, 1), (10, 132)]
    (codeMat 115) (codeMat 500) (codeMat 94) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit214_lb16_wc

theorem plane463GenSource0045 :
    QuotientRankAtLeast (spanCodes [275, 133, 68, 54, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 136, 96, 20, 1] [(275, 275), (133, 232), (68, 411), (54, 1), (10, 399)]
    (codeMat 499) (codeMat 445) (codeMat 478) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit236_lb16_wc

theorem plane463GenSource0046 :
    QuotientRankAtLeast (spanCodes [262, 147, 68, 32, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 96, 20, 10, 1] [(262, 287), (147, 21), (68, 353), (32, 256), (10, 383)]
    (codeMat 190) (codeMat 467) (codeMat 339) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit164_lb16_wc

theorem plane463GenSource0047 :
    QuotientRankAtLeast (spanCodes [263, 146, 68, 33, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 96, 20, 10, 1] [(263, 373), (146, 256), (68, 30), (33, 21), (10, 383)]
    (codeMat 478) (codeMat 169) (codeMat 225) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit164_lb16_wc

theorem plane463GenSource0048 :
    QuotientRankAtLeast (spanCodes [273, 132, 68, 55, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 132, 96, 10, 1] [(273, 142), (132, 97), (68, 96), (55, 402), (10, 132)]
    (codeMat 92) (codeMat 226) (codeMat 141) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit214_lb16_wc

theorem plane463GenSource0049 :
    QuotientRankAtLeast (spanCodes [275, 134, 68, 53, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 132, 96, 10, 1] [(275, 285), (134, 374), (68, 228), (53, 133), (10, 132)]
    (codeMat 123) (codeMat 244) (codeMat 95) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit214_lb16_wc

end QiushiMatmul
