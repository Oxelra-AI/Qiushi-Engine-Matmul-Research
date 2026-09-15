import QiushiPlane453GenData
import QiushiCertifiedTransport
import QiushiStep133Mono393From243
import QiushiWcOrbit156Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane453GenSource0010 :
    QuotientRankAtLeast (spanCodes [389, 68, 20, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 68, 20, 10] [(389, 68), (68, 322), (20, 280), (10, 80)]
    (codeMat 93) (codeMat 318) (codeMat 299) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit393_lb17_mono

theorem plane453GenSource0011 :
    QuotientRankAtLeast (spanCodes [422, 68, 20, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 68, 20, 10] [(422, 274), (68, 78), (20, 262), (10, 68)]
    (codeMat 177) (codeMat 417) (codeMat 177) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit393_lb17_mono

theorem plane453GenSource0012 :
    QuotientRankAtLeast (spanCodes [423, 68, 20, 10]) 17 := by
  apply quotientRankAtLeast_weaken (n := 17) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 68, 20, 10] [(423, 342), (68, 78), (20, 322), (10, 68)]
    (codeMat 241) (codeMat 423) (codeMat 181) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit393_lb17_mono

theorem plane453GenSource0013 :
    QuotientRankAtLeast (spanCodes [68, 33, 20, 8, 2]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [68, 32, 20, 10, 1] [(68, 80), (33, 10), (20, 20), (8, 1), (2, 32)]
    (codeMat 266) (codeMat 161) (codeMat 161) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit156_lb16_wc

theorem plane453GenSource0014 :
    QuotientRankAtLeast (spanCodes [68, 37, 20, 9, 3]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [68, 32, 20, 10, 1] [(68, 91), (37, 10), (20, 43), (9, 1), (3, 63)]
    (codeMat 275) (codeMat 181) (codeMat 423) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit156_lb16_wc

theorem plane453GenSource0015 :
    QuotientRankAtLeast (spanCodes [68, 37, 20, 8, 2]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [68, 32, 20, 10, 1] [(68, 112), (37, 62), (20, 52), (8, 1), (2, 32)]
    (codeMat 266) (codeMat 417) (codeMat 177) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit156_lb16_wc

theorem plane453GenSource0016 :
    QuotientRankAtLeast (spanCodes [68, 38, 20, 10, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [68, 32, 20, 10, 1] [(68, 69), (38, 43), (20, 30), (10, 10), (1, 1)]
    (codeMat 281) (codeMat 279) (codeMat 279) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit156_lb16_wc

theorem plane453GenSource0017 :
    QuotientRankAtLeast (spanCodes [129, 68, 20, 8, 2]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [68, 32, 20, 10, 1] [(129, 10), (68, 80), (20, 68), (8, 32), (2, 1)]
    (codeMat 161) (codeMat 266) (codeMat 266) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit156_lb16_wc

theorem plane453GenSource0018 :
    QuotientRankAtLeast (spanCodes [133, 68, 20, 9, 3]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [68, 32, 20, 10, 1] [(133, 91), (68, 80), (20, 101), (9, 32), (3, 1)]
    (codeMat 233) (codeMat 314) (codeMat 271) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit156_lb16_wc

theorem plane453GenSource0019 :
    QuotientRankAtLeast (spanCodes [133, 68, 20, 8, 2]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [68, 32, 20, 10, 1] [(133, 78), (68, 112), (20, 68), (8, 32), (2, 1)]
    (codeMat 177) (codeMat 266) (codeMat 266) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit156_lb16_wc

end QiushiMatmul
