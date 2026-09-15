import QiushiPlane470GenData
import QiushiCertifiedTransport
import QiushiStep99Orbit196Dispatch
import QiushiWcOrbit164Dispatch
import QiushiWcOrbit214Dispatch
import QiushiWcOrbit216Dispatch
import QiushiWcOrbit236Dispatch
import QiushiWcOrbit238Dispatch
import QiushiWcOrbit75Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane470GenSource0060 :
    QuotientRankAtLeast (spanCodes [259, 163, 66, 22, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 132, 96, 10, 1] [(259, 374), (163, 499), (66, 238), (22, 132), (10, 278)]
    (codeMat 215) (codeMat 458) (codeMat 458) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit214_lb16_wc

theorem plane470GenSource0061 :
    QuotientRankAtLeast (spanCodes [259, 132, 84, 50, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [294, 136, 96, 20, 1] [(259, 20), (132, 306), (84, 339), (50, 462), (10, 463)]
    (codeMat 298) (codeMat 239) (codeMat 351) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit238_lb16_wc

theorem plane470GenSource0062 :
    QuotientRankAtLeast (spanCodes [259, 144, 84, 38, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 132, 96, 10, 1] [(259, 10), (144, 504), (84, 499), (38, 238), (10, 408)]
    (codeMat 485) (codeMat 244) (codeMat 95) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit214_lb16_wc

theorem plane470GenSource0063 :
    QuotientRankAtLeast (spanCodes [259, 145, 84, 39, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 132, 32, 10, 1] [(259, 441), (145, 435), (84, 165), (39, 440), (10, 408)]
    (codeMat 159) (codeMat 87) (codeMat 468) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit196_lb16_unconditional

theorem plane470GenSource0064 :
    QuotientRankAtLeast (spanCodes [259, 150, 84, 32, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 136, 96, 20, 1] [(259, 399), (150, 97), (84, 157), (32, 1), (10, 263)]
    (codeMat 250) (codeMat 141) (codeMat 226) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit236_lb16_wc

theorem plane470GenSource0065 :
    QuotientRankAtLeast (spanCodes [259, 161, 67, 23, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 96, 20, 10, 1] [(259, 126), (161, 267), (67, 127), (23, 362), (10, 383)]
    (codeMat 468) (codeMat 470) (codeMat 213) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit164_lb16_wc

theorem plane470GenSource0066 :
    QuotientRankAtLeast (spanCodes [259, 163, 65, 21, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [294, 136, 96, 20, 1] [(259, 96), (163, 156), (65, 1), (21, 430), (10, 326)]
    (codeMat 317) (codeMat 419) (codeMat 183) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit238_lb16_wc

theorem plane470GenSource0067 :
    QuotientRankAtLeast (spanCodes [259, 129, 82, 49, 10, 6]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 160, 68, 20, 10, 1] [(259, 31), (129, 21), (82, 170), (49, 69), (10, 322), (6, 1)]
    (codeMat 161) (codeMat 117) (codeMat 380) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit75_lb16_wc

theorem plane470GenSource0068 :
    QuotientRankAtLeast (spanCodes [259, 135, 84, 48, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 132, 32, 10, 1] [(259, 175), (135, 278), (84, 317), (48, 1), (10, 435)]
    (codeMat 442) (codeMat 445) (codeMat 478) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit196_lb16_unconditional

theorem plane470GenSource0069 :
    QuotientRankAtLeast (spanCodes [259, 146, 84, 37, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [294, 132, 96, 10, 1] [(259, 238), (146, 1), (84, 419), (37, 228), (10, 457)]
    (codeMat 183) (codeMat 111) (codeMat 412) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit216_lb16_wc

end QiushiMatmul
