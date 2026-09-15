import QiushiPlane456GenData
import QiushiCertifiedTransport
import QiushiStep126Mono175From75
import QiushiWcOrbit201Dispatch
import QiushiWcOrbit235Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane456GenSource0000 :
    QuotientRankAtLeast (spanCodes [132, 69, 37, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [326, 136, 38, 20, 1] [(132, 508), (69, 475), (37, 338), (20, 509), (10, 21)]
    (codeMat 342) (codeMat 303) (codeMat 286) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit235_lb16_wc

theorem plane456GenSource0001 :
    QuotientRankAtLeast (spanCodes [132, 71, 37, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [340, 132, 32, 10, 1] [(132, 496), (71, 497), (37, 383), (20, 464), (10, 42)]
    (codeMat 405) (codeMat 281) (codeMat 281) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit201_lb16_wc

theorem plane456GenSource0002 :
    QuotientRankAtLeast (spanCodes [130, 64, 35, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [340, 132, 32, 10, 1] [(130, 32), (64, 1), (35, 175), (20, 341), (10, 42)]
    (codeMat 340) (codeMat 277) (codeMat 277) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit201_lb16_wc

theorem plane456GenSource0003 :
    QuotientRankAtLeast (spanCodes [130, 71, 35, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [340, 132, 32, 10, 1] [(130, 1), (71, 497), (35, 341), (20, 506), (10, 42)]
    (codeMat 477) (codeMat 303) (codeMat 286) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit201_lb16_wc

theorem plane456GenSource0004 :
    QuotientRankAtLeast (spanCodes [132, 64, 37, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [340, 132, 32, 10, 1] [(132, 132), (64, 32), (37, 464), (20, 133), (10, 42)]
    (codeMat 270) (codeMat 266) (codeMat 266) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit201_lb16_wc

theorem plane456GenSource0005 :
    QuotientRankAtLeast (spanCodes [131, 71, 34, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [340, 132, 32, 10, 1] [(131, 175), (71, 497), (34, 10), (20, 11), (10, 42)]
    (codeMat 467) (codeMat 125) (codeMat 348) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit201_lb16_wc

theorem plane456GenSource0006 :
    QuotientRankAtLeast (spanCodes [257, 161, 19, 10, 7]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [326, 136, 38, 20, 1] [(257, 326), (161, 174), (19, 20), (10, 50), (7, 1)]
    (codeMat 273) (codeMat 348) (codeMat 125) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit235_lb16_wc

theorem plane456GenSource0007 :
    QuotientRankAtLeast (spanCodes [257, 130, 35, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [326, 136, 38, 20, 1] [(257, 137), (130, 1), (35, 175), (20, 21), (10, 509)]
    (codeMat 397) (codeMat 111) (codeMat 412) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit235_lb16_wc

theorem plane456GenSource0008 :
    QuotientRankAtLeast (spanCodes [263, 132, 37, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 160, 20, 10, 1] [(263, 191), (132, 21), (37, 180), (20, 20), (10, 434)]
    (codeMat 206) (codeMat 110) (codeMat 444) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit175_lb16_mono

theorem plane456GenSource0009 :
    QuotientRankAtLeast (spanCodes [256, 130, 35, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [340, 132, 32, 10, 1] [(256, 32), (130, 1), (35, 341), (20, 42), (10, 133)]
    (codeMat 277) (codeMat 98) (codeMat 140) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit201_lb16_wc

end QiushiMatmul
