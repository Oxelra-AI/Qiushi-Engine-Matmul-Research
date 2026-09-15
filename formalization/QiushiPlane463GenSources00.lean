import QiushiPlane463GenData
import QiushiCertifiedTransport
import QiushiWcOrbit201Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane463GenSource0000 :
    QuotientRankAtLeast (spanCodes [131, 68, 36, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [340, 132, 32, 10, 1] [(131, 383), (68, 475), (36, 32), (20, 33), (10, 42)]
    (codeMat 346) (codeMat 459) (codeMat 346) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit201_lb16_wc

theorem plane463GenSource0001 :
    QuotientRankAtLeast (spanCodes [131, 68, 39, 23, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [340, 132, 32, 10, 1] [(131, 175), (68, 497), (39, 43), (23, 11), (10, 42)]
    (codeMat 467) (codeMat 377) (codeMat 369) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit201_lb16_wc

theorem plane463GenSource0002 :
    QuotientRankAtLeast (spanCodes [130, 68, 37, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [340, 132, 32, 10, 1] [(130, 32), (68, 475), (37, 383), (20, 464), (10, 42)]
    (codeMat 342) (codeMat 281) (codeMat 281) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit201_lb16_wc

theorem plane463GenSource0003 :
    QuotientRankAtLeast (spanCodes [130, 68, 38, 23, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [340, 132, 32, 10, 1] [(130, 1), (68, 497), (38, 133), (23, 506), (10, 42)]
    (codeMat 477) (codeMat 271) (codeMat 314) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit201_lb16_wc

theorem plane463GenSource0004 :
    QuotientRankAtLeast (spanCodes [129, 68, 36, 22, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [340, 132, 32, 10, 1] [(129, 175), (68, 497), (36, 1), (22, 11), (10, 42)]
    (codeMat 403) (codeMat 93) (codeMat 372) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit201_lb16_wc

theorem plane463GenSource0005 :
    QuotientRankAtLeast (spanCodes [129, 68, 39, 21, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [340, 132, 32, 10, 1] [(129, 383), (68, 475), (39, 10), (21, 33), (10, 42)]
    (codeMat 282) (codeMat 239) (codeMat 351) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit201_lb16_wc

theorem plane463GenSource0006 :
    QuotientRankAtLeast (spanCodes [128, 68, 37, 22, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [340, 132, 32, 10, 1] [(128, 1), (68, 497), (37, 175), (22, 506), (10, 42)]
    (codeMat 412) (codeMat 299) (codeMat 318) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit201_lb16_wc

theorem plane463GenSource0007 :
    QuotientRankAtLeast (spanCodes [128, 68, 38, 21, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [340, 132, 32, 10, 1] [(128, 32), (68, 475), (38, 341), (21, 464), (10, 42)]
    (codeMat 279) (codeMat 317) (codeMat 285) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit201_lb16_wc

theorem plane463GenSource0008 :
    QuotientRankAtLeast (spanCodes [135, 68, 33, 21, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [340, 132, 32, 10, 1] [(135, 507), (68, 475), (33, 383), (21, 506), (10, 42)]
    (codeMat 351) (codeMat 267) (codeMat 282) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit201_lb16_wc

theorem plane463GenSource0009 :
    QuotientRankAtLeast (spanCodes [135, 68, 35, 23, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [340, 132, 32, 10, 1] [(135, 496), (68, 497), (35, 133), (23, 464), (10, 42)]
    (codeMat 405) (codeMat 285) (codeMat 317) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit201_lb16_wc

end QiushiMatmul
