import QiushiPlane468GenData
import QiushiCertifiedTransport
import QiushiStep99Orbit196Dispatch
import QiushiStep99Orbit217Dispatch
import QiushiWcOrbit213Dispatch
import QiushiWcOrbit214Dispatch
import QiushiWcOrbit218Dispatch
import QiushiWcOrbit235Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane468GenSource0050 :
    QuotientRankAtLeast (spanCodes [278, 128, 84, 36, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 132, 32, 10, 1] [(278, 11), (128, 32), (84, 311), (36, 1), (10, 440)]
    (codeMat 307) (codeMat 84) (codeMat 84) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit196_lb16_unconditional

theorem plane468GenSource0051 :
    QuotientRankAtLeast (spanCodes [290, 164, 68, 16, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 132, 32, 10, 1] [(290, 42), (164, 43), (68, 441), (16, 32), (10, 316)]
    (codeMat 181) (codeMat 117) (codeMat 380) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit196_lb16_unconditional

theorem plane468GenSource0052 :
    QuotientRankAtLeast (spanCodes [293, 164, 67, 23, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [310, 132, 96, 10, 1] [(293, 10), (164, 434), (67, 96), (23, 316), (10, 97)]
    (codeMat 335) (codeMat 161) (codeMat 161) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit218_lb16_wc

theorem plane468GenSource0053 :
    QuotientRankAtLeast (spanCodes [260, 147, 84, 55, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 132, 96, 10, 1] [(260, 1), (147, 278), (84, 285), (55, 374), (10, 402)]
    (codeMat 229) (codeMat 204) (codeMat 114) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit214_lb16_wc

theorem plane468GenSource0054 :
    QuotientRankAtLeast (spanCodes [262, 145, 84, 53, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 132, 32, 10, 1] [(262, 175), (145, 408), (84, 142), (53, 434), (10, 435)]
    (codeMat 443) (codeMat 431) (codeMat 477) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit196_lb16_unconditional

theorem plane468GenSource0055 :
    QuotientRankAtLeast (spanCodes [295, 164, 64, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 132, 32, 10, 1] [(295, 408), (164, 42), (64, 1), (20, 175), (10, 441)]
    (codeMat 444) (codeMat 407) (codeMat 405) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit196_lb16_unconditional

theorem plane468GenSource0056 :
    QuotientRankAtLeast (spanCodes [261, 149, 84, 49, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [276, 132, 96, 10, 1] [(261, 373), (149, 10), (84, 286), (49, 496), (10, 400)]
    (codeMat 143) (codeMat 348) (codeMat 125) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit213_lb16_wc

theorem plane468GenSource0057 :
    QuotientRankAtLeast (spanCodes [289, 164, 64, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [326, 136, 38, 20, 1] [(289, 352), (164, 39), (64, 1), (20, 475), (10, 137)]
    (codeMat 124) (codeMat 275) (codeMat 275) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit235_lb16_wc

theorem plane468GenSource0058 :
    QuotientRankAtLeast (spanCodes [278, 132, 84, 32, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 132, 32, 10, 1] [(278, 132), (132, 278), (84, 317), (32, 32), (10, 408)]
    (codeMat 214) (codeMat 465) (codeMat 465) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit196_lb16_unconditional

theorem plane468GenSource0059 :
    QuotientRankAtLeast (spanCodes [291, 164, 65, 21, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [308, 132, 96, 10, 1] [(291, 464), (164, 475), (65, 1), (21, 308), (10, 97)]
    (codeMat 461) (codeMat 421) (codeMat 179) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit217_lb16_unconditional

end QiushiMatmul
