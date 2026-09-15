import QiushiPlane425GenData
import QiushiCertifiedTransport
import QiushiWcOrbit156Dispatch
import QiushiWcOrbit161Dispatch
import QiushiWcOrbit164Dispatch
import QiushiWcOrbit194Dispatch
import QiushiWcOrbit201Dispatch
import QiushiWcOrbit264Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane425GenSource0010 :
    QuotientRankAtLeast (spanCodes [258, 66, 10, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 12, 2, 1] [(258, 268), (66, 12), (10, 14), (1, 1)]
    (codeMat 305) (codeMat 277) (codeMat 277) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit264_lb16_wc

theorem plane425GenSource0011 :
    QuotientRankAtLeast (spanCodes [258, 68, 36, 10, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [68, 32, 20, 10, 1] [(258, 80), (68, 10), (36, 32), (10, 69), (1, 1)]
    (codeMat 225) (codeMat 161) (codeMat 161) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit156_lb16_wc

theorem plane425GenSource0012 :
    QuotientRankAtLeast (spanCodes [258, 68, 38, 10, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [68, 32, 20, 10, 1] [(258, 91), (68, 10), (38, 100), (10, 69), (1, 1)]
    (codeMat 233) (codeMat 165) (codeMat 163) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit156_lb16_wc

theorem plane425GenSource0013 :
    QuotientRankAtLeast (spanCodes [258, 68, 32, 10, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [68, 32, 20, 10, 1] [(258, 80), (68, 10), (32, 32), (10, 68), (1, 1)]
    (codeMat 161) (codeMat 161) (codeMat 161) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit156_lb16_wc

theorem plane425GenSource0014 :
    QuotientRankAtLeast (spanCodes [258, 68, 34, 10, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [68, 32, 20, 10, 1] [(258, 91), (68, 10), (34, 100), (10, 68), (1, 1)]
    (codeMat 169) (codeMat 165) (codeMat 163) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit156_lb16_wc

theorem plane425GenSource0015 :
    QuotientRankAtLeast (spanCodes [258, 100, 22, 10, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 96, 20, 10, 1] [(258, 362), (100, 96), (22, 21), (10, 11), (1, 1)]
    (codeMat 473) (codeMat 277) (codeMat 277) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit164_lb16_wc

theorem plane425GenSource0016 :
    QuotientRankAtLeast (spanCodes [258, 68, 50, 10, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [288, 68, 20, 10, 1] [(258, 30), (68, 11), (50, 366), (10, 78), (1, 1)]
    (codeMat 417) (codeMat 181) (codeMat 423) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit161_lb16_wc

theorem plane425GenSource0017 :
    QuotientRankAtLeast (spanCodes [258, 148, 52, 10, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [340, 132, 32, 10, 1] [(258, 506), (148, 133), (52, 42), (10, 11), (1, 1)]
    (codeMat 473) (codeMat 309) (codeMat 309) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit201_lb16_wc

theorem plane425GenSource0018 :
    QuotientRankAtLeast (spanCodes [258, 150, 54, 10, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 96, 20, 10, 1] [(258, 31), (150, 20), (54, 1), (10, 352), (1, 256)]
    (codeMat 115) (codeMat 116) (codeMat 92) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit164_lb16_wc

theorem plane425GenSource0019 :
    QuotientRankAtLeast (spanCodes [258, 134, 36, 10, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 132, 32, 10, 1] [(258, 262), (134, 132), (36, 32), (10, 11), (1, 1)]
    (codeMat 345) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit194_lb16_wc

end QiushiMatmul
