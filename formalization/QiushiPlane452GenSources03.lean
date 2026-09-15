import QiushiPlane452GenData
import QiushiCertifiedTransport
import QiushiWcOrbit201Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane452GenSource0030 :
    QuotientRankAtLeast (spanCodes [128, 65, 35, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [340, 132, 32, 10, 1] [(128, 32), (65, 1), (35, 175), (20, 341), (10, 42)]
    (codeMat 277) (codeMat 277) (codeMat 277) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit201_lb16_wc

theorem plane452GenSource0031 :
    QuotientRankAtLeast (spanCodes [130, 64, 35, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [340, 132, 32, 10, 1] [(130, 32), (64, 1), (35, 175), (20, 341), (10, 42)]
    (codeMat 340) (codeMat 277) (codeMat 277) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit201_lb16_wc

theorem plane452GenSource0032 :
    QuotientRankAtLeast (spanCodes [129, 66, 35, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [340, 132, 32, 10, 1] [(129, 11), (66, 10), (35, 506), (20, 175), (10, 42)]
    (codeMat 397) (codeMat 314) (codeMat 271) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit201_lb16_wc

theorem plane452GenSource0033 :
    QuotientRankAtLeast (spanCodes [130, 71, 35, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [340, 132, 32, 10, 1] [(130, 1), (71, 497), (35, 341), (20, 506), (10, 42)]
    (codeMat 477) (codeMat 303) (codeMat 286) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit201_lb16_wc

theorem plane452GenSource0034 :
    QuotientRankAtLeast (spanCodes [133, 64, 35, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [340, 132, 32, 10, 1] [(133, 164), (64, 32), (35, 506), (20, 175), (10, 42)]
    (codeMat 271) (codeMat 314) (codeMat 271) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit201_lb16_wc

theorem plane452GenSource0035 :
    QuotientRankAtLeast (spanCodes [135, 65, 35, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [340, 132, 32, 10, 1] [(135, 164), (65, 32), (35, 506), (20, 175), (10, 42)]
    (codeMat 334) (codeMat 314) (codeMat 271) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit201_lb16_wc

theorem plane452GenSource0036 :
    QuotientRankAtLeast (spanCodes [132, 67, 35, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [340, 132, 32, 10, 1] [(132, 373), (67, 43), (35, 175), (20, 341), (10, 42)]
    (codeMat 407) (codeMat 277) (codeMat 277) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit201_lb16_wc

theorem plane452GenSource0037 :
    QuotientRankAtLeast (spanCodes [257, 65, 35, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [340, 132, 32, 10, 1] [(257, 33), (65, 32), (35, 383), (20, 175), (10, 341)]
    (codeMat 340) (codeMat 174) (codeMat 359) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit201_lb16_wc

theorem plane452GenSource0038 :
    QuotientRankAtLeast (spanCodes [263, 71, 35, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [340, 132, 32, 10, 1] [(263, 132), (71, 164), (35, 133), (20, 506), (10, 175)]
    (codeMat 271) (codeMat 157) (codeMat 486) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit201_lb16_wc

theorem plane452GenSource0039 :
    QuotientRankAtLeast (spanCodes [258, 67, 35, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [340, 132, 32, 10, 1] [(258, 350), (67, 373), (35, 383), (20, 175), (10, 341)]
    (codeMat 470) (codeMat 174) (codeMat 359) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit201_lb16_wc

end QiushiMatmul
