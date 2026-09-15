import QiushiPlane470LowerGenData
import QiushiCertifiedTransport
import QiushiStep126Mono245From75
import QiushiStep128Mono244From75
import QiushiWcOrbit213Dispatch
import QiushiWcOrbit235Dispatch
import QiushiWcOrbit236Dispatch
import QiushiWcOrbit238Dispatch
import QiushiWcOrbit241Dispatch
import QiushiWcOrbit242Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane470LowerGenSource0040 :
    QuotientRankAtLeast (spanCodes [259, 128, 84, 38, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 136, 96, 20, 1] [(259, 136), (128, 1), (84, 157), (38, 507), (10, 263)]
    (codeMat 172) (codeMat 355) (codeMat 190) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit236_lb16_wc

theorem plane470LowerGenSource0041 :
    QuotientRankAtLeast (spanCodes [259, 129, 84, 38, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 162, 68, 19, 10] [(259, 258), (129, 68), (84, 426), (38, 245), (10, 332)]
    (codeMat 372) (codeMat 419) (codeMat 183) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit241_lb16_wc

theorem plane470LowerGenSource0042 :
    QuotientRankAtLeast (spanCodes [259, 129, 84, 49, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [133, 68, 35, 20, 10] [(259, 145), (129, 78), (84, 172), (49, 178), (10, 121)]
    (codeMat 477) (codeMat 254) (codeMat 443) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit244_lb16_mono

theorem plane470LowerGenSource0043 :
    QuotientRankAtLeast (spanCodes [259, 128, 84, 49, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [294, 136, 96, 20, 1] [(259, 136), (128, 1), (84, 156), (49, 430), (10, 326)]
    (codeMat 428) (codeMat 355) (codeMat 190) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit238_lb16_wc

theorem plane470LowerGenSource0044 :
    QuotientRankAtLeast (spanCodes [259, 129, 84, 51, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 164, 68, 19, 10] [(259, 332), (129, 189), (84, 428), (51, 243), (10, 341)]
    (codeMat 415) (codeMat 158) (codeMat 358) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit242_lb16_wc

theorem plane470LowerGenSource0045 :
    QuotientRankAtLeast (spanCodes [259, 132, 84, 55, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [294, 136, 96, 20, 1] [(259, 338), (132, 21), (84, 474), (55, 326), (10, 430)]
    (codeMat 494) (codeMat 117) (codeMat 380) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit238_lb16_wc

theorem plane470LowerGenSource0046 :
    QuotientRankAtLeast (spanCodes [259, 128, 84, 52, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 136, 96, 20, 1] [(259, 398), (128, 1), (84, 116), (52, 20), (10, 262)]
    (codeMat 156) (codeMat 98) (codeMat 140) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit236_lb16_wc

theorem plane470LowerGenSource0047 :
    QuotientRankAtLeast (spanCodes [259, 129, 84, 52, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [276, 132, 96, 10, 1] [(259, 287), (129, 228), (84, 106), (52, 506), (10, 383)]
    (codeMat 279) (codeMat 498) (codeMat 206) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit213_lb16_wc

theorem plane470LowerGenSource0048 :
    QuotientRankAtLeast (spanCodes [259, 129, 84, 55, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 161, 68, 20, 10] [(259, 30), (129, 20), (84, 161), (55, 68), (10, 262)]
    (codeMat 225) (codeMat 116) (codeMat 92) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit245_lb16_mono

theorem plane470LowerGenSource0049 :
    QuotientRankAtLeast (spanCodes [259, 128, 84, 55, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [326, 136, 38, 20, 1] [(259, 136), (128, 1), (84, 156), (55, 373), (10, 326)]
    (codeMat 428) (codeMat 355) (codeMat 190) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit235_lb16_wc

end QiushiMatmul
