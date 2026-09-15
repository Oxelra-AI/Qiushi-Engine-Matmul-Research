import QiushiPlane475GenData
import QiushiCertifiedTransport
import QiushiStep99Orbit196Dispatch
import QiushiWcOrbit164Dispatch
import QiushiWcOrbit201Dispatch
import QiushiWcOrbit213Dispatch
import QiushiWcOrbit214Dispatch
import QiushiWcOrbit75Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane475GenSource0030 :
    QuotientRankAtLeast (spanCodes [258, 148, 81, 49, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 132, 96, 10, 1] [(258, 381), (148, 97), (81, 228), (49, 238), (10, 374)]
    (codeMat 486) (codeMat 187) (codeMat 229) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit214_lb16_wc

theorem plane475GenSource0031 :
    QuotientRankAtLeast (spanCodes [276, 130, 71, 39, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 132, 96, 10, 1] [(276, 11), (130, 1), (71, 132), (39, 408), (10, 96)]
    (codeMat 85) (codeMat 102) (codeMat 156) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit214_lb16_wc

theorem plane475GenSource0032 :
    QuotientRankAtLeast (spanCodes [263, 131, 70, 38, 21, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 160, 68, 20, 10, 1] [(263, 429), (131, 274), (70, 228), (38, 488), (21, 80), (10, 160)]
    (codeMat 87) (codeMat 340) (codeMat 85) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit75_lb16_wc

theorem plane475GenSource0033 :
    QuotientRankAtLeast (spanCodes [305, 160, 96, 10, 5]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [340, 132, 32, 10, 1] [(305, 382), (160, 497), (96, 496), (10, 132), (5, 32)]
    (codeMat 92) (codeMat 482) (codeMat 143) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit201_lb16_wc

theorem plane475GenSource0034 :
    QuotientRankAtLeast (spanCodes [263, 151, 82, 50, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 96, 20, 10, 1] [(263, 126), (151, 96), (82, 383), (50, 363), (10, 362)]
    (codeMat 498) (codeMat 426) (codeMat 335) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit164_lb16_wc

theorem plane475GenSource0035 :
    QuotientRankAtLeast (spanCodes [273, 129, 68, 36, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [276, 132, 96, 10, 1] [(273, 106), (129, 400), (68, 132), (36, 1), (10, 96)]
    (codeMat 99) (codeMat 212) (codeMat 86) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit213_lb16_wc

theorem plane475GenSource0036 :
    QuotientRankAtLeast (spanCodes [274, 130, 71, 39, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [340, 132, 32, 10, 1] [(274, 507), (130, 1), (71, 497), (39, 164), (10, 132)]
    (codeMat 213) (codeMat 359) (codeMat 174) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit201_lb16_wc

theorem plane475GenSource0037 :
    QuotientRankAtLeast (spanCodes [279, 135, 66, 34, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 96, 20, 10, 1] [(279, 372), (135, 21), (66, 383), (34, 126), (10, 127)]
    (codeMat 426) (codeMat 342) (codeMat 215) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit164_lb16_wc

theorem plane475GenSource0038 :
    QuotientRankAtLeast (spanCodes [288, 165, 96, 21, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 132, 32, 10, 1] [(288, 1), (165, 285), (96, 33), (21, 278), (10, 175)]
    (codeMat 486) (codeMat 85) (codeMat 340) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit196_lb16_unconditional

theorem plane475GenSource0039 :
    QuotientRankAtLeast (spanCodes [292, 165, 96, 17, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 132, 96, 10, 1] [(292, 504), (165, 106), (96, 238), (17, 10), (10, 11)]
    (codeMat 331) (codeMat 313) (codeMat 313) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit214_lb16_wc

end QiushiMatmul
