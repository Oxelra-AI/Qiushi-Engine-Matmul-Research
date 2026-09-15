import QiushiPlane463GenData
import QiushiCertifiedTransport
import QiushiWcOrbit164Dispatch
import QiushiWcOrbit214Dispatch
import QiushiWcOrbit236Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane463GenSource0060 :
    QuotientRankAtLeast (spanCodes [262, 134, 68, 53, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 96, 20, 10, 1] [(262, 10), (134, 11), (68, 30), (53, 127), (10, 383)]
    (codeMat 236) (codeMat 117) (codeMat 380) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit164_lb16_wc

theorem plane463GenSource0061 :
    QuotientRankAtLeast (spanCodes [263, 135, 68, 52, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 96, 20, 10, 1] [(263, 96), (135, 97), (68, 353), (52, 362), (10, 383)]
    (codeMat 340) (codeMat 443) (codeMat 254) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit164_lb16_wc

theorem plane463GenSource0062 :
    QuotientRankAtLeast (spanCodes [273, 145, 68, 34, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 132, 96, 10, 1] [(273, 106), (145, 402), (68, 96), (34, 133), (10, 132)]
    (codeMat 106) (codeMat 340) (codeMat 85) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit214_lb16_wc

theorem plane463GenSource0063 :
    QuotientRankAtLeast (spanCodes [274, 146, 68, 33, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 132, 96, 10, 1] [(274, 505), (146, 1), (68, 228), (33, 402), (10, 132)]
    (codeMat 87) (codeMat 358) (codeMat 158) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit214_lb16_wc

theorem plane463GenSource0064 :
    QuotientRankAtLeast (spanCodes [272, 151, 68, 36, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 136, 96, 20, 1] [(272, 506), (151, 232), (68, 20), (36, 1), (10, 399)]
    (codeMat 355) (codeMat 157) (codeMat 486) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit236_lb16_wc

theorem plane463GenSource0065 :
    QuotientRankAtLeast (spanCodes [274, 149, 68, 38, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 136, 96, 20, 1] [(274, 263), (149, 21), (68, 411), (38, 252), (10, 399)]
    (codeMat 311) (codeMat 254) (codeMat 443) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit236_lb16_wc

theorem plane463GenSource0066 :
    QuotientRankAtLeast (spanCodes [262, 128, 68, 51, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 96, 20, 10, 1] [(262, 257), (128, 256), (68, 353), (51, 362), (10, 383)]
    (codeMat 285) (codeMat 397) (codeMat 250) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit164_lb16_wc

theorem plane463GenSource0067 :
    QuotientRankAtLeast (spanCodes [263, 129, 68, 50, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 96, 20, 10, 1] [(263, 20), (129, 21), (68, 30), (50, 127), (10, 383)]
    (codeMat 165) (codeMat 499) (codeMat 382) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit164_lb16_wc

theorem plane463GenSource0068 :
    QuotientRankAtLeast (spanCodes [273, 151, 68, 36, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 132, 96, 10, 1] [(273, 142), (151, 374), (68, 96), (36, 1), (10, 132)]
    (codeMat 99) (codeMat 212) (codeMat 86) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit214_lb16_wc

theorem plane463GenSource0069 :
    QuotientRankAtLeast (spanCodes [275, 149, 68, 38, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 132, 96, 10, 1] [(275, 409), (149, 97), (68, 228), (38, 278), (10, 132)]
    (codeMat 95) (codeMat 230) (codeMat 159) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit214_lb16_wc

end QiushiMatmul
