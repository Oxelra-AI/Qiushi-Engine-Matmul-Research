import QiushiPlane468GenData
import QiushiCertifiedTransport
import QiushiStep99Orbit196Dispatch
import QiushiWcOrbit201Dispatch
import QiushiWcOrbit213Dispatch
import QiushiWcOrbit214Dispatch
import QiushiWcOrbit218Dispatch
import QiushiWcOrbit238Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane468GenSource0030 :
    QuotientRankAtLeast (spanCodes [277, 146, 84, 54, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 132, 96, 10, 1] [(277, 409), (146, 1), (84, 239), (54, 504), (10, 133)]
    (codeMat 407) (codeMat 358) (codeMat 158) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit214_lb16_wc

theorem plane468GenSource0031 :
    QuotientRankAtLeast (spanCodes [278, 145, 84, 53, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [294, 136, 96, 20, 1] [(278, 136), (145, 430), (84, 156), (53, 462), (10, 463)]
    (codeMat 299) (codeMat 345) (codeMat 345) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit238_lb16_wc

theorem plane468GenSource0032 :
    QuotientRankAtLeast (spanCodes [259, 130, 84, 38, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [310, 132, 96, 10, 1] [(259, 132), (130, 1), (84, 143), (38, 96), (10, 440)]
    (codeMat 93) (codeMat 331) (codeMat 410) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit218_lb16_wc

theorem plane468GenSource0033 :
    QuotientRankAtLeast (spanCodes [272, 145, 84, 53, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [310, 132, 96, 10, 1] [(272, 343), (145, 310), (84, 107), (53, 435), (10, 434)]
    (codeMat 491) (codeMat 372) (codeMat 93) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit218_lb16_wc

theorem plane468GenSource0034 :
    QuotientRankAtLeast (spanCodes [278, 151, 84, 51, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [276, 132, 96, 10, 1] [(278, 507), (151, 383), (84, 382), (51, 96), (10, 496)]
    (codeMat 85) (codeMat 254) (codeMat 443) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit213_lb16_wc

theorem plane468GenSource0035 :
    QuotientRankAtLeast (spanCodes [279, 150, 84, 50, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [276, 132, 96, 10, 1] [(279, 106), (150, 238), (84, 382), (50, 497), (10, 496)]
    (codeMat 298) (codeMat 244) (codeMat 95) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit213_lb16_wc

theorem plane468GenSource0036 :
    QuotientRankAtLeast (spanCodes [261, 135, 84, 35, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [294, 136, 96, 20, 1] [(261, 475), (135, 137), (84, 431), (35, 462), (10, 306)]
    (codeMat 311) (codeMat 372) (codeMat 93) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit238_lb16_wc

theorem plane468GenSource0037 :
    QuotientRankAtLeast (spanCodes [272, 146, 84, 54, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [340, 132, 32, 10, 1] [(272, 42), (146, 1), (84, 372), (54, 32), (10, 507)]
    (codeMat 247) (codeMat 110) (codeMat 444) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit201_lb16_wc

theorem plane468GenSource0038 :
    QuotientRankAtLeast (spanCodes [288, 162, 82, 10, 6]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 132, 32, 10, 1] [(288, 32), (162, 43), (82, 175), (10, 441), (6, 1)]
    (codeMat 417) (codeMat 122) (codeMat 460) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit196_lb16_unconditional

theorem plane468GenSource0039 :
    QuotientRankAtLeast (spanCodes [259, 128, 84, 36, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [340, 132, 32, 10, 1] [(259, 496), (128, 32), (84, 372), (36, 1), (10, 507)]
    (codeMat 355) (codeMat 141) (codeMat 226) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit201_lb16_wc

end QiushiMatmul
