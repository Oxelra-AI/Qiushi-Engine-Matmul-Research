import QiushiPlane470GenData
import QiushiCertifiedTransport
import QiushiStep99Orbit196Dispatch
import QiushiWcOrbit164Dispatch
import QiushiWcOrbit194Dispatch
import QiushiWcOrbit235Dispatch
import QiushiWcOrbit236Dispatch
import QiushiWcOrbit238Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane470GenSource0040 :
    QuotientRankAtLeast (spanCodes [259, 151, 84, 49, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 132, 32, 10, 1] [(259, 33), (151, 133), (84, 165), (49, 435), (10, 408)]
    (codeMat 372) (codeMat 236) (codeMat 123) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit196_lb16_unconditional

theorem plane470GenSource0041 :
    QuotientRankAtLeast (spanCodes [259, 161, 83, 10, 7]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 96, 20, 10, 1] [(259, 257), (161, 267), (83, 21), (10, 383), (7, 256)]
    (codeMat 117) (codeMat 93) (codeMat 372) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit164_lb16_wc

theorem plane470GenSource0042 :
    QuotientRankAtLeast (spanCodes [259, 163, 81, 10, 5]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [294, 136, 96, 20, 1] [(259, 294), (163, 474), (81, 430), (10, 326), (5, 1)]
    (codeMat 249) (codeMat 339) (codeMat 467) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit238_lb16_wc

theorem plane470GenSource0043 :
    QuotientRankAtLeast (spanCodes [259, 134, 84, 33, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [326, 136, 38, 20, 1] [(259, 508), (134, 475), (84, 156), (33, 373), (10, 326)]
    (codeMat 382) (codeMat 485) (codeMat 171) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit235_lb16_wc

theorem plane470GenSource0044 :
    QuotientRankAtLeast (spanCodes [259, 135, 84, 32, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [326, 136, 38, 20, 1] [(259, 462), (135, 175), (84, 156), (32, 1), (10, 326)]
    (codeMat 250) (codeMat 143) (codeMat 482) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit235_lb16_wc

theorem plane470GenSource0045 :
    QuotientRankAtLeast (spanCodes [259, 144, 84, 55, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 132, 32, 10, 1] [(259, 284), (144, 1), (84, 317), (55, 408), (10, 435)]
    (codeMat 382) (codeMat 334) (codeMat 442) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit196_lb16_unconditional

theorem plane470GenSource0046 :
    QuotientRankAtLeast (spanCodes [259, 134, 84, 54, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 132, 32, 10, 1] [(259, 164), (134, 393), (84, 142), (54, 1), (10, 295)]
    (codeMat 307) (codeMat 443) (codeMat 254) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit194_lb16_wc

theorem plane470GenSource0047 :
    QuotientRankAtLeast (spanCodes [259, 145, 84, 32, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [294, 136, 96, 20, 1] [(259, 462), (145, 430), (84, 156), (32, 1), (10, 326)]
    (codeMat 250) (codeMat 143) (codeMat 482) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit238_lb16_wc

theorem plane470GenSource0048 :
    QuotientRankAtLeast (spanCodes [259, 164, 65, 21, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [294, 136, 96, 20, 1] [(259, 97), (164, 475), (65, 1), (21, 232), (10, 326)]
    (codeMat 309) (codeMat 421) (codeMat 179) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit238_lb16_wc

theorem plane470GenSource0049 :
    QuotientRankAtLeast (spanCodes [259, 134, 84, 52, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 136, 96, 20, 1] [(259, 96), (134, 232), (84, 358), (52, 371), (10, 399)]
    (codeMat 358) (codeMat 477) (codeMat 431) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit236_lb16_wc

end QiushiMatmul
