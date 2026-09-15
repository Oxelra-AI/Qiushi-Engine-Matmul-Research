import QiushiPlane452GenData
import QiushiCertifiedTransport
import QiushiStep132Mono384From243
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane452GenSource0010 :
    QuotientRankAtLeast (spanCodes [196, 35, 20, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [68, 35, 20, 10] [(196, 68), (35, 41), (20, 61), (10, 55)]
    (codeMat 337) (codeMat 478) (codeMat 445) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit384_lb17_mono

theorem plane452GenSource0011 :
    QuotientRankAtLeast (spanCodes [199, 35, 20, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [68, 35, 20, 10] [(199, 68), (35, 41), (20, 61), (10, 55)]
    (codeMat 273) (codeMat 478) (codeMat 445) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit384_lb17_mono

theorem plane452GenSource0012 :
    QuotientRankAtLeast (spanCodes [257, 35, 20, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [68, 35, 20, 10] [(257, 109), (35, 55), (20, 10), (10, 30)]
    (codeMat 282) (codeMat 87) (codeMat 468) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit384_lb17_mono

theorem plane452GenSource0013 :
    QuotientRankAtLeast (spanCodes [258, 35, 20, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [68, 35, 20, 10] [(258, 68), (35, 10), (20, 41), (10, 61)]
    (codeMat 337) (codeMat 207) (codeMat 370) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit384_lb17_mono

theorem plane452GenSource0014 :
    QuotientRankAtLeast (spanCodes [261, 35, 20, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [68, 35, 20, 10] [(261, 80), (35, 41), (20, 55), (10, 35)]
    (codeMat 267) (codeMat 159) (codeMat 230) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit384_lb17_mono

theorem plane452GenSource0015 :
    QuotientRankAtLeast (spanCodes [262, 35, 20, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [68, 35, 20, 10] [(262, 68), (35, 10), (20, 41), (10, 61)]
    (codeMat 273) (codeMat 207) (codeMat 370) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit384_lb17_mono

theorem plane452GenSource0016 :
    QuotientRankAtLeast (spanCodes [322, 35, 20, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [68, 35, 20, 10] [(322, 68), (35, 30), (20, 35), (10, 20)]
    (codeMat 273) (codeMat 172) (codeMat 99) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit384_lb17_mono

theorem plane452GenSource0017 :
    QuotientRankAtLeast (spanCodes [323, 35, 20, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [68, 35, 20, 10] [(323, 80), (35, 61), (20, 30), (10, 20)]
    (codeMat 267) (codeMat 468) (codeMat 87) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit384_lb17_mono

theorem plane452GenSource0018 :
    QuotientRankAtLeast (spanCodes [326, 35, 20, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [68, 35, 20, 10] [(326, 109), (35, 35), (20, 61), (10, 20)]
    (codeMat 282) (codeMat 380) (codeMat 117) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit384_lb17_mono

theorem plane452GenSource0019 :
    QuotientRankAtLeast (spanCodes [327, 35, 20, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [68, 35, 20, 10] [(327, 68), (35, 30), (20, 35), (10, 20)]
    (codeMat 337) (codeMat 172) (codeMat 99) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit384_lb17_mono

end QiushiMatmul
