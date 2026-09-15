import QiushiPlane456GenData
import QiushiCertifiedTransport
import QiushiStep99Orbit196Dispatch
import QiushiWcOrbit161Dispatch
import QiushiWcOrbit164Dispatch
import QiushiWcOrbit201Dispatch
import QiushiWcOrbit214Dispatch
import QiushiWcOrbit218Dispatch
import QiushiWcOrbit75Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane456GenSource0050 :
    QuotientRankAtLeast (spanCodes [259, 161, 103, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 132, 32, 10, 1] [(259, 133), (161, 317), (103, 279), (20, 408), (10, 435)]
    (codeMat 486) (codeMat 473) (codeMat 409) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit196_lb16_unconditional

theorem plane456GenSource0051 :
    QuotientRankAtLeast (spanCodes [261, 161, 97, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 96, 20, 10, 1] [(261, 363), (161, 372), (97, 373), (20, 287), (10, 126)]
    (codeMat 444) (codeMat 254) (codeMat 443) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit164_lb16_wc

theorem plane456GenSource0052 :
    QuotientRankAtLeast (spanCodes [263, 132, 70, 37, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 160, 68, 20, 10, 1] [(263, 429), (132, 329), (70, 274), (37, 488), (20, 328), (10, 80)]
    (codeMat 86) (codeMat 270) (codeMat 298) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit75_lb16_wc

theorem plane456GenSource0053 :
    QuotientRankAtLeast (spanCodes [323, 134, 39, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [288, 68, 20, 10, 1] [(323, 91), (134, 319), (39, 21), (20, 31), (10, 20)]
    (codeMat 339) (codeMat 492) (codeMat 115) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit161_lb16_wc

theorem plane456GenSource0054 :
    QuotientRankAtLeast (spanCodes [258, 129, 70, 32, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 160, 68, 20, 10, 1] [(258, 328), (129, 160), (70, 240), (32, 1), (20, 68), (10, 262)]
    (codeMat 106) (codeMat 204) (codeMat 114) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit75_lb16_wc

theorem plane456GenSource0055 :
    QuotientRankAtLeast (spanCodes [327, 130, 35, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [340, 132, 32, 10, 1] [(327, 11), (130, 1), (35, 341), (20, 133), (10, 506)]
    (codeMat 397) (codeMat 334) (codeMat 442) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit201_lb16_wc

theorem plane456GenSource0056 :
    QuotientRankAtLeast (spanCodes [260, 161, 97, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 132, 96, 10, 1] [(260, 1), (161, 498), (97, 10), (20, 97), (10, 381)]
    (codeMat 405) (codeMat 142) (codeMat 354) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit214_lb16_wc

theorem plane456GenSource0057 :
    QuotientRankAtLeast (spanCodes [294, 161, 67, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [310, 132, 96, 10, 1] [(294, 435), (161, 467), (67, 440), (20, 238), (10, 441)]
    (codeMat 303) (codeMat 181) (codeMat 423) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit218_lb16_wc

theorem plane456GenSource0058 :
    QuotientRankAtLeast (spanCodes [322, 134, 39, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 96, 20, 10, 1] [(322, 97), (134, 276), (39, 30), (20, 20), (10, 31)]
    (codeMat 459) (codeMat 489) (codeMat 241) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit164_lb16_wc

theorem plane456GenSource0059 :
    QuotientRankAtLeast (spanCodes [324, 128, 33, 20, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 132, 32, 10, 1] [(324, 441), (128, 1), (33, 278), (20, 434), (10, 132)]
    (codeMat 212) (codeMat 355) (codeMat 190) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit196_lb16_unconditional

end QiushiMatmul
