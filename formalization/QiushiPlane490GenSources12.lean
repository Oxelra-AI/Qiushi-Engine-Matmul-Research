import QiushiPlane490GenData
import QiushiCertifiedTransport
import QiushiPlane267GenFinal
import QiushiPlane298GenFinal
import QiushiWcOrbit281Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane490GenSource0120 :
    QuotientRankAtLeast (spanCodes [272, 9, 4, 3]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [84, 32, 2, 1] [(272, 118), (9, 32), (4, 1), (3, 2)]
    (codeMat 281) (codeMat 212) (codeMat 86) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane267Gen_lb16

theorem plane490GenSource0121 :
    QuotientRankAtLeast (spanCodes [256, 17, 8, 2]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 16, 10, 1] [(256, 256), (17, 10), (8, 1), (2, 16)]
    (codeMat 266) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit281_lb16_wc

theorem plane490GenSource0122 :
    QuotientRankAtLeast (spanCodes [256, 18, 10, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 16, 10, 1] [(256, 256), (18, 27), (10, 26), (1, 16)]
    (codeMat 266) (codeMat 282) (codeMat 267) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit281_lb16_wc

theorem plane490GenSource0123 :
    QuotientRankAtLeast (spanCodes [273, 32, 8, 2]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [84, 32, 2, 1] [(273, 84), (32, 1), (8, 2), (2, 32)]
    (codeMat 266) (codeMat 140) (codeMat 98) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane267Gen_lb16

theorem plane490GenSource0124 :
    QuotientRankAtLeast (spanCodes [272, 36, 9, 3]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [84, 32, 2, 1] [(272, 118), (36, 1), (9, 2), (3, 32)]
    (codeMat 267) (codeMat 156) (codeMat 102) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane267Gen_lb16

theorem plane490GenSource0125 :
    QuotientRankAtLeast (spanCodes [260, 39, 23, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [384, 32, 10, 1] [(260, 384), (39, 43), (23, 11), (10, 42)]
    (codeMat 339) (codeMat 377) (codeMat 369) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane298Gen_lb16

theorem plane490GenSource0126 :
    QuotientRankAtLeast (spanCodes [257, 32, 18, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [84, 32, 2, 1] [(257, 118), (32, 1), (18, 32), (10, 34)]
    (codeMat 282) (codeMat 204) (codeMat 114) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane267Gen_lb16

theorem plane490GenSource0127 :
    QuotientRankAtLeast (spanCodes [260, 34, 23, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [384, 32, 10, 1] [(260, 384), (34, 43), (23, 33), (10, 42)]
    (codeMat 346) (codeMat 491) (codeMat 375) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane298Gen_lb16

theorem plane490GenSource0128 :
    QuotientRankAtLeast (spanCodes [275, 51, 10, 6]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [384, 32, 10, 1] [(275, 395), (51, 11), (10, 42), (6, 1)]
    (codeMat 409) (codeMat 499) (codeMat 382) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane298Gen_lb16

theorem plane490GenSource0129 :
    QuotientRankAtLeast (spanCodes [257, 36, 18, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [84, 32, 2, 1] [(257, 118), (36, 1), (18, 2), (10, 34)]
    (codeMat 275) (codeMat 92) (codeMat 116) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.plane267Gen_lb16

end QiushiMatmul
