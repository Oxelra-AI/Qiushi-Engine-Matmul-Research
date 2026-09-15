import QiushiPlane425GenData
import QiushiCertifiedTransport
import QiushiStep99Orbit196Dispatch
import QiushiWcOrbit156Dispatch
import QiushiWcOrbit164Dispatch
import QiushiWcOrbit194Dispatch
import QiushiWcOrbit201Dispatch
import QiushiWcOrbit96Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane425GenSource0020 :
    QuotientRankAtLeast (spanCodes [258, 148, 48, 10, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 96, 20, 10, 1] [(258, 31), (148, 20), (48, 1), (10, 96), (1, 256)]
    (codeMat 122) (codeMat 116) (codeMat 92) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit164_lb16_wc

theorem plane425GenSource0021 :
    QuotientRankAtLeast (spanCodes [258, 150, 50, 10, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [340, 132, 32, 10, 1] [(258, 506), (150, 133), (50, 42), (10, 10), (1, 1)]
    (codeMat 401) (codeMat 309) (codeMat 309) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit201_lb16_wc

theorem plane425GenSource0022 :
    QuotientRankAtLeast (spanCodes [258, 150, 48, 10, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 132, 32, 10, 1] [(258, 434), (150, 132), (48, 32), (10, 10), (1, 1)]
    (codeMat 401) (codeMat 305) (codeMat 305) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit196_lb16_unconditional

theorem plane425GenSource0023 :
    QuotientRankAtLeast (spanCodes [258, 148, 36, 10, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 132, 32, 10, 1] [(258, 294), (148, 132), (36, 32), (10, 11), (1, 1)]
    (codeMat 409) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit194_lb16_wc

theorem plane425GenSource0024 :
    QuotientRankAtLeast (spanCodes [258, 134, 48, 10, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 132, 32, 10, 1] [(258, 386), (134, 132), (48, 32), (10, 10), (1, 1)]
    (codeMat 273) (codeMat 305) (codeMat 305) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit194_lb16_wc

theorem plane425GenSource0025 :
    QuotientRankAtLeast (spanCodes [258, 128, 64, 10, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [68, 20, 8, 2, 1] [(258, 20), (128, 2), (64, 1), (10, 80), (1, 8)]
    (codeMat 140) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit96_lb16_wc

theorem plane425GenSource0026 :
    QuotientRankAtLeast (spanCodes [258, 144, 80, 10, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [68, 32, 20, 10, 1] [(258, 100), (144, 63), (80, 62), (10, 20), (1, 32)]
    (codeMat 92) (codeMat 282) (codeMat 267) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit156_lb16_wc

theorem plane425GenSource0027 :
    QuotientRankAtLeast (spanCodes [258, 162, 98, 10, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 132, 32, 10, 1] [(258, 42), (162, 175), (98, 174), (10, 300), (1, 32)]
    (codeMat 396) (codeMat 226) (codeMat 141) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit194_lb16_wc

theorem plane425GenSource0028 :
    QuotientRankAtLeast (spanCodes [258, 128, 68, 10, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [68, 32, 20, 10, 1] [(258, 20), (128, 32), (68, 10), (10, 68), (1, 1)]
    (codeMat 161) (codeMat 161) (codeMat 161) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit156_lb16_wc

theorem plane425GenSource0029 :
    QuotientRankAtLeast (spanCodes [258, 166, 98, 10, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 132, 32, 10, 1] [(258, 42), (166, 133), (98, 142), (10, 284), (1, 32)]
    (codeMat 397) (codeMat 242) (codeMat 205) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit196_lb16_unconditional

end QiushiMatmul
