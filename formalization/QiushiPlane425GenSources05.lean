import QiushiPlane425GenData
import QiushiCertifiedTransport
import QiushiOrbit31FP
import QiushiStep99Orbit150Dispatch
import QiushiStep99Orbit196Dispatch
import QiushiWcOrbit194Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane425GenSource0050 :
    QuotientRankAtLeast (spanCodes [258, 134, 96, 10, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 132, 32, 10, 1] [(258, 310), (134, 402), (96, 11), (10, 316), (1, 32)]
    (codeMat 102) (codeMat 190) (codeMat 355) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit196_lb16_unconditional

theorem plane425GenSource0051 :
    QuotientRankAtLeast (spanCodes [258, 146, 116, 10, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 132, 32, 10, 1] [(258, 440), (146, 32), (116, 142), (10, 11), (1, 1)]
    (codeMat 473) (codeMat 305) (codeMat 305) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit196_lb16_unconditional

theorem plane425GenSource0052 :
    QuotientRankAtLeast (spanCodes [258, 212, 50, 10, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 132, 32, 10, 1] [(258, 435), (212, 142), (50, 43), (10, 11), (1, 1)]
    (codeMat 401) (codeMat 307) (codeMat 311) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit196_lb16_unconditional

theorem plane425GenSource0053 :
    QuotientRankAtLeast (spanCodes [258, 180, 68, 10, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 68, 16, 10, 1] [(258, 326), (180, 349), (68, 69), (10, 78), (1, 1)]
    (codeMat 305) (codeMat 405) (codeMat 407) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit150_lb16_unconditional

theorem plane425GenSource0054 :
    QuotientRankAtLeast (spanCodes [258, 214, 36, 10, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 132, 32, 10, 1] [(258, 295), (214, 142), (36, 32), (10, 10), (1, 1)]
    (codeMat 409) (codeMat 275) (codeMat 275) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit194_lb16_wc

theorem plane425GenSource0055 :
    QuotientRankAtLeast (spanCodes [258, 198, 50, 10, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 132, 32, 10, 1] [(258, 387), (198, 133), (50, 43), (10, 11), (1, 1)]
    (codeMat 273) (codeMat 307) (codeMat 311) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit194_lb16_wc

theorem plane425GenSource0056 :
    QuotientRankAtLeast (spanCodes [258, 148, 98, 10, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 132, 32, 10, 1] [(258, 408), (148, 43), (98, 174), (10, 316), (1, 32)]
    (codeMat 271) (codeMat 370) (codeMat 207) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit196_lb16_unconditional

theorem plane425GenSource0057 :
    QuotientRankAtLeast (spanCodes [258, 178, 68, 10, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 68, 16, 10, 1] [(258, 327), (178, 343), (68, 69), (10, 79), (1, 1)]
    (codeMat 305) (codeMat 407) (codeMat 405) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit150_lb16_unconditional

theorem plane425GenSource0058 :
    QuotientRankAtLeast (spanCodes [258, 32, 16, 10, 4, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68] [(258, 80), (32, 1), (16, 2), (10, 20), (4, 8), (1, 32)]
    (codeMat 266) (codeMat 84) (codeMat 84) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit31_lb15

theorem plane425GenSource0059 :
    QuotientRankAtLeast (spanCodes [258, 32, 18, 10, 4, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68] [(258, 112), (32, 1), (18, 54), (10, 52), (4, 8), (1, 32)]
    (codeMat 266) (codeMat 212) (codeMat 86) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit31_lb15

end QiushiMatmul
