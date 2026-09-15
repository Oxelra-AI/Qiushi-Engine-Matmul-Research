import QiushiPlane428GenData
import QiushiCertifiedTransport
import QiushiMonoOrbit93From29
import QiushiWcOrbit156Dispatch
import QiushiWcOrbit194Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane428GenSource0010 :
    QuotientRankAtLeast (spanCodes [136, 66, 34, 16, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [68, 32, 20, 10, 1] [(136, 10), (66, 20), (34, 68), (16, 1), (1, 32)]
    (codeMat 98) (codeMat 266) (codeMat 266) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit156_lb16_wc

theorem plane428GenSource0011 :
    QuotientRankAtLeast (spanCodes [258, 74, 42, 16, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 132, 32, 10, 1] [(258, 392), (74, 268), (42, 10), (16, 1), (1, 32)]
    (codeMat 266) (codeMat 354) (codeMat 142) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit194_lb16_wc

theorem plane428GenSource0012 :
    QuotientRankAtLeast (spanCodes [266, 66, 34, 16, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 132, 32, 10, 1] [(266, 142), (66, 268), (34, 10), (16, 1), (1, 32)]
    (codeMat 394) (codeMat 98) (codeMat 140) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit194_lb16_wc

theorem plane428GenSource0013 :
    QuotientRankAtLeast (spanCodes [262, 74, 42, 16, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 132, 32, 10, 1] [(262, 392), (74, 300), (42, 10), (16, 1), (1, 32)]
    (codeMat 330) (codeMat 354) (codeMat 142) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit194_lb16_wc

theorem plane428GenSource0014 :
    QuotientRankAtLeast (spanCodes [270, 66, 34, 16, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 132, 32, 10, 1] [(270, 142), (66, 300), (34, 10), (16, 1), (1, 32)]
    (codeMat 458) (codeMat 98) (codeMat 140) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit194_lb16_wc

theorem plane428GenSource0015 :
    QuotientRankAtLeast (spanCodes [386, 74, 42, 16, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 132, 32, 10, 1] [(386, 392), (74, 268), (42, 11), (16, 1), (1, 32)]
    (codeMat 266) (codeMat 358) (codeMat 158) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit194_lb16_wc

theorem plane428GenSource0016 :
    QuotientRankAtLeast (spanCodes [394, 66, 34, 16, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 132, 32, 10, 1] [(394, 142), (66, 268), (34, 11), (16, 1), (1, 32)]
    (codeMat 394) (codeMat 102) (codeMat 156) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit194_lb16_wc

theorem plane428GenSource0017 :
    QuotientRankAtLeast (spanCodes [388, 74, 42, 16, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 132, 32, 10, 1] [(388, 392), (74, 300), (42, 11), (16, 1), (1, 32)]
    (codeMat 330) (codeMat 358) (codeMat 158) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit194_lb16_wc

theorem plane428GenSource0018 :
    QuotientRankAtLeast (spanCodes [396, 66, 34, 16, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 132, 32, 10, 1] [(396, 142), (66, 300), (34, 11), (16, 1), (1, 32)]
    (codeMat 458) (codeMat 102) (codeMat 156) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit194_lb16_wc

theorem plane428GenSource0019 :
    QuotientRankAtLeast (spanCodes [96, 16, 8, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [68, 16, 8, 2, 1] [(96, 68), (16, 2), (8, 1), (2, 16), (1, 8)]
    (codeMat 266) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit93_lb15_mono

end QiushiMatmul
