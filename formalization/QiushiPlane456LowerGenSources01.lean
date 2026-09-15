import QiushiPlane456LowerGenData
import QiushiCertifiedTransport
import QiushiMonoOrbit370From196
import QiushiStep126Mono175From75
import QiushiWcOrbit201Dispatch
import QiushiWcOrbit235Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane456LowerGenSource0010 :
    QuotientRankAtLeast (spanCodes [132, 69, 37, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [326, 136, 38, 20, 1] [(132, 508), (69, 475), (37, 338), (20, 509), (10, 21)]
    (codeMat 342) (codeMat 303) (codeMat 286) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit235_lb16_wc

theorem plane456LowerGenSource0011 :
    QuotientRankAtLeast (spanCodes [132, 71, 37, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [340, 132, 32, 10, 1] [(132, 496), (71, 497), (37, 383), (20, 464), (10, 42)]
    (codeMat 405) (codeMat 281) (codeMat 281) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit201_lb16_wc

theorem plane456LowerGenSource0012 :
    QuotientRankAtLeast (spanCodes [130, 64, 35, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [340, 132, 32, 10, 1] [(130, 32), (64, 1), (35, 175), (20, 341), (10, 42)]
    (codeMat 340) (codeMat 277) (codeMat 277) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit201_lb16_wc

theorem plane456LowerGenSource0013 :
    QuotientRankAtLeast (spanCodes [130, 71, 35, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [340, 132, 32, 10, 1] [(130, 1), (71, 497), (35, 341), (20, 506), (10, 42)]
    (codeMat 477) (codeMat 303) (codeMat 286) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit201_lb16_wc

theorem plane456LowerGenSource0014 :
    QuotientRankAtLeast (spanCodes [132, 64, 37, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [340, 132, 32, 10, 1] [(132, 132), (64, 32), (37, 464), (20, 133), (10, 42)]
    (codeMat 270) (codeMat 266) (codeMat 266) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit201_lb16_wc

theorem plane456LowerGenSource0015 :
    QuotientRankAtLeast (spanCodes [129, 69, 32, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 160, 20, 10, 1] [(129, 180), (69, 441), (32, 1), (20, 11), (10, 20)]
    (codeMat 410) (codeMat 92) (codeMat 116) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit175_lb16_mono

theorem plane456LowerGenSource0016 :
    QuotientRankAtLeast (spanCodes [130, 69, 35, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 160, 20, 10, 1] [(130, 1), (69, 441), (35, 160), (20, 434), (10, 20)]
    (codeMat 213) (codeMat 299) (codeMat 318) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit175_lb16_mono

theorem plane456LowerGenSource0017 :
    QuotientRankAtLeast (spanCodes [161, 103, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [334, 160, 20, 1] [(161, 346), (103, 161), (20, 495), (10, 21)]
    (codeMat 286) (codeMat 285) (codeMat 317) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit370_lb16_mono

theorem plane456LowerGenSource0018 :
    QuotientRankAtLeast (spanCodes [257, 161, 19, 10, 7]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [326, 136, 38, 20, 1] [(257, 326), (161, 174), (19, 20), (10, 50), (7, 1)]
    (codeMat 273) (codeMat 348) (codeMat 125) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit235_lb16_wc

theorem plane456LowerGenSource0019 :
    QuotientRankAtLeast (spanCodes [262, 160, 20, 10, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 160, 20, 10, 1] [(262, 262), (160, 160), (20, 20), (10, 10), (1, 1)]
    (codeMat 273) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit175_lb16_mono

end QiushiMatmul
