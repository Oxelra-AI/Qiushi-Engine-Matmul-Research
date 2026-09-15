import QiushiPlane464GenData
import QiushiCertifiedTransport
import QiushiWcOrbit164Dispatch
import QiushiWcOrbit201Dispatch
import QiushiWcOrbit213Dispatch
import QiushiWcOrbit214Dispatch
import QiushiWcOrbit236Dispatch
import QiushiWcOrbit238Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane464GenSource0040 :
    QuotientRankAtLeast (spanCodes [275, 149, 68, 33, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 96, 20, 10, 1] [(275, 382), (149, 383), (68, 363), (33, 373), (10, 276)]
    (codeMat 477) (codeMat 124) (codeMat 124) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit164_lb16_wc

theorem plane464GenSource0041 :
    QuotientRankAtLeast (spanCodes [276, 146, 68, 38, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [340, 132, 32, 10, 1] [(276, 33), (146, 32), (68, 497), (38, 43), (10, 373)]
    (codeMat 501) (codeMat 117) (codeMat 380) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit201_lb16_wc

theorem plane464GenSource0042 :
    QuotientRankAtLeast (spanCodes [279, 145, 68, 37, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [276, 132, 96, 10, 1] [(279, 372), (145, 373), (68, 506), (37, 383), (10, 411)]
    (codeMat 181) (codeMat 115) (codeMat 492) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit213_lb16_wc

theorem plane464GenSource0043 :
    QuotientRankAtLeast (spanCodes [256, 135, 68, 51, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [340, 132, 32, 10, 1] [(256, 1), (135, 43), (68, 11), (51, 475), (10, 164)]
    (codeMat 236) (codeMat 156) (codeMat 102) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit201_lb16_wc

theorem plane464GenSource0044 :
    QuotientRankAtLeast (spanCodes [258, 133, 68, 49, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [340, 132, 32, 10, 1] [(258, 506), (133, 464), (68, 383), (49, 43), (10, 350)]
    (codeMat 423) (codeMat 445) (codeMat 478) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit201_lb16_wc

theorem plane464GenSource0045 :
    QuotientRankAtLeast (spanCodes [274, 149, 68, 33, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 136, 96, 20, 1] [(274, 262), (149, 506), (68, 371), (33, 232), (10, 136)]
    (codeMat 215) (codeMat 313) (codeMat 313) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit236_lb16_wc

theorem plane464GenSource0046 :
    QuotientRankAtLeast (spanCodes [276, 147, 68, 39, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [294, 136, 96, 20, 1] [(276, 430), (147, 338), (68, 462), (39, 20), (10, 21)]
    (codeMat 403) (codeMat 491) (codeMat 375) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit238_lb16_wc

theorem plane464GenSource0047 :
    QuotientRankAtLeast (spanCodes [291, 164, 68, 16, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 132, 96, 10, 1] [(291, 278), (164, 96), (68, 228), (16, 1), (10, 10)]
    (codeMat 282) (codeMat 267) (codeMat 282) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit214_lb16_wc

theorem plane464GenSource0048 :
    QuotientRankAtLeast (spanCodes [277, 149, 68, 33, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [340, 132, 32, 10, 1] [(277, 165), (149, 164), (68, 497), (33, 350), (10, 373)]
    (codeMat 500) (codeMat 499) (codeMat 382) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit201_lb16_wc

theorem plane464GenSource0049 :
    QuotientRankAtLeast (spanCodes [279, 151, 68, 35, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [276, 132, 96, 10, 1] [(279, 277), (151, 276), (68, 506), (35, 228), (10, 411)]
    (codeMat 244) (codeMat 501) (codeMat 494) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit213_lb16_wc

end QiushiMatmul
