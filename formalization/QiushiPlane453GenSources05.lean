import QiushiPlane453GenData
import QiushiCertifiedTransport
import QiushiStep99Orbit150Dispatch
import QiushiStep99Orbit217Dispatch
import QiushiWcOrbit194Dispatch
import QiushiWcOrbit201Dispatch
import QiushiWcOrbit238Dispatch
import QiushiWcOrbit75Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane453GenSource0050 :
    QuotientRankAtLeast (spanCodes [294, 161, 68, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [294, 136, 96, 20, 1] [(294, 136), (161, 339), (68, 295), (20, 232), (10, 430)]
    (codeMat 382) (codeMat 377) (codeMat 369) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit238_lb16_wc

theorem plane453GenSource0051 :
    QuotientRankAtLeast (spanCodes [258, 162, 68, 20, 10, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 160, 68, 20, 10, 1] [(258, 508), (162, 228), (68, 79), (20, 263), (10, 68), (1, 1)]
    (codeMat 177) (codeMat 421) (codeMat 179) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit75_lb16_wc

theorem plane453GenSource0052 :
    QuotientRankAtLeast (spanCodes [289, 131, 68, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [340, 132, 32, 10, 1] [(289, 43), (131, 175), (68, 350), (20, 164), (10, 383)]
    (codeMat 254) (codeMat 369) (codeMat 377) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit201_lb16_wc

theorem plane453GenSource0053 :
    QuotientRankAtLeast (spanCodes [295, 133, 68, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [340, 132, 32, 10, 1] [(295, 10), (133, 497), (68, 350), (20, 475), (10, 383)]
    (codeMat 190) (codeMat 247) (codeMat 379) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit201_lb16_wc

theorem plane453GenSource0054 :
    QuotientRankAtLeast (spanCodes [385, 68, 35, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [340, 132, 32, 10, 1] [(385, 43), (68, 350), (35, 464), (20, 506), (10, 383)]
    (codeMat 407) (codeMat 443) (codeMat 254) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit201_lb16_wc

theorem plane453GenSource0055 :
    QuotientRankAtLeast (spanCodes [391, 68, 37, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [340, 132, 32, 10, 1] [(391, 43), (68, 350), (37, 175), (20, 133), (10, 383)]
    (codeMat 415) (codeMat 397) (codeMat 250) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit201_lb16_wc

theorem plane453GenSource0056 :
    QuotientRankAtLeast (spanCodes [260, 167, 68, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [308, 132, 96, 10, 1] [(260, 1), (167, 443), (68, 433), (20, 97), (10, 341)]
    (codeMat 405) (codeMat 207) (codeMat 370) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit217_lb16_unconditional

theorem plane453GenSource0057 :
    QuotientRankAtLeast (spanCodes [417, 68, 20, 8, 2]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 132, 32, 10, 1] [(417, 142), (68, 295), (20, 11), (8, 32), (2, 1)]
    (codeMat 465) (codeMat 102) (codeMat 156) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit194_lb16_wc

theorem plane453GenSource0058 :
    QuotientRankAtLeast (spanCodes [418, 68, 20, 10, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 68, 16, 10, 1] [(418, 349), (68, 78), (20, 326), (10, 69), (1, 1)]
    (codeMat 177) (codeMat 419) (codeMat 183) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit150_lb16_unconditional

theorem plane453GenSource0059 :
    QuotientRankAtLeast (spanCodes [420, 68, 20, 10, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 68, 16, 10, 1] [(420, 343), (68, 79), (20, 327), (10, 69), (1, 1)]
    (codeMat 177) (codeMat 423) (codeMat 181) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit150_lb16_unconditional

end QiushiMatmul
