import QiushiPlane455GenData
import QiushiCertifiedTransport
import QiushiStep133Mono393From243
import QiushiStep133Mono397From243
import QiushiWcOrbit156Dispatch
import QiushiWcOrbit201Dispatch
import QiushiWcOrbit322Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane455GenSource0010 :
    QuotientRankAtLeast (spanCodes [324, 129, 20, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [135, 96, 20, 10] [(324, 20), (129, 10), (20, 231), (10, 153)]
    (codeMat 485) (codeMat 282) (codeMat 267) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit397_lb17_mono

theorem plane455GenSource0011 :
    QuotientRankAtLeast (spanCodes [327, 129, 20, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [135, 96, 20, 10] [(327, 153), (129, 10), (20, 237), (10, 30)]
    (codeMat 428) (codeMat 275) (codeMat 275) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit397_lb17_mono

theorem plane455GenSource0012 :
    QuotientRankAtLeast (spanCodes [352, 129, 20, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [308, 160, 10, 1] [(352, 319), (129, 160), (20, 170), (10, 308)]
    (codeMat 271) (codeMat 372) (codeMat 93) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit322_lb17_wc

theorem plane455GenSource0013 :
    QuotientRankAtLeast (spanCodes [353, 129, 20, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 68, 20, 10] [(353, 322), (129, 268), (20, 280), (10, 328)]
    (codeMat 206) (codeMat 485) (codeMat 171) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit393_lb17_mono

theorem plane455GenSource0014 :
    QuotientRankAtLeast (spanCodes [356, 129, 20, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 68, 20, 10] [(356, 78), (129, 274), (20, 322), (10, 262)]
    (codeMat 115) (codeMat 380) (codeMat 117) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit393_lb17_mono

theorem plane455GenSource0015 :
    QuotientRankAtLeast (spanCodes [129, 33, 16, 10, 4]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [68, 32, 20, 10, 1] [(129, 80), (33, 20), (16, 1), (10, 10), (4, 32)]
    (codeMat 266) (codeMat 266) (codeMat 266) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit156_lb16_wc

theorem plane455GenSource0016 :
    QuotientRankAtLeast (spanCodes [128, 68, 20, 10, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [68, 32, 20, 10, 1] [(128, 32), (68, 68), (20, 80), (10, 10), (1, 1)]
    (codeMat 273) (codeMat 273) (codeMat 273) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit156_lb16_wc

theorem plane455GenSource0017 :
    QuotientRankAtLeast (spanCodes [129, 69, 20, 9, 3]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [68, 32, 20, 10, 1] [(129, 62), (69, 112), (20, 101), (9, 32), (3, 1)]
    (codeMat 249) (codeMat 314) (codeMat 271) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit156_lb16_wc

theorem plane455GenSource0018 :
    QuotientRankAtLeast (spanCodes [128, 70, 20, 10, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [68, 32, 20, 10, 1] [(128, 32), (70, 68), (20, 80), (10, 11), (1, 1)]
    (codeMat 281) (codeMat 305) (codeMat 305) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit156_lb16_wc

theorem plane455GenSource0019 :
    QuotientRankAtLeast (spanCodes [129, 66, 35, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [340, 132, 32, 10, 1] [(129, 11), (66, 10), (35, 506), (20, 175), (10, 42)]
    (codeMat 397) (codeMat 314) (codeMat 271) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit201_lb16_wc

end QiushiMatmul
