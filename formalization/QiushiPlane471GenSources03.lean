import QiushiPlane471GenData
import QiushiCertifiedTransport
import QiushiStep99Orbit196Dispatch
import QiushiWcOrbit164Dispatch
import QiushiWcOrbit213Dispatch
import QiushiWcOrbit214Dispatch
import QiushiWcOrbit236Dispatch
import QiushiWcOrbit238Dispatch
import QiushiWcOrbit75Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane471GenSource0030 :
    QuotientRankAtLeast (spanCodes [276, 150, 84, 53, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 132, 96, 10, 1] [(276, 374), (150, 402), (84, 142), (53, 96), (10, 97)]
    (codeMat 115) (codeMat 247) (codeMat 379) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit214_lb16_wc

theorem plane471GenSource0031 :
    QuotientRankAtLeast (spanCodes [277, 151, 84, 52, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 132, 96, 10, 1] [(277, 107), (151, 238), (84, 239), (52, 381), (10, 97)]
    (codeMat 285) (codeMat 226) (codeMat 141) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit214_lb16_wc

theorem plane471GenSource0032 :
    QuotientRankAtLeast (spanCodes [260, 129, 84, 37, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 136, 96, 20, 1] [(260, 1), (129, 263), (84, 410), (37, 399), (10, 252)]
    (codeMat 317) (codeMat 95) (codeMat 244) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit236_lb16_wc

theorem plane471GenSource0033 :
    QuotientRankAtLeast (spanCodes [263, 130, 84, 38, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [294, 136, 96, 20, 1] [(263, 462), (130, 1), (84, 442), (38, 21), (10, 327)]
    (codeMat 477) (codeMat 102) (codeMat 156) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit238_lb16_wc

theorem plane471GenSource0034 :
    QuotientRankAtLeast (spanCodes [256, 133, 84, 33, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 96, 20, 10, 1] [(256, 256), (133, 287), (84, 116), (33, 383), (10, 362)]
    (codeMat 279) (codeMat 473) (codeMat 409) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit164_lb16_wc

theorem plane471GenSource0035 :
    QuotientRankAtLeast (spanCodes [279, 146, 84, 54, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 132, 32, 10, 1] [(279, 165), (146, 1), (84, 311), (54, 32), (10, 440)]
    (codeMat 95) (codeMat 335) (codeMat 426) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit196_lb16_unconditional

theorem plane471GenSource0036 :
    QuotientRankAtLeast (spanCodes [274, 151, 84, 51, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 96, 20, 10, 1] [(274, 11), (151, 363), (84, 107), (51, 353), (10, 287)]
    (codeMat 359) (codeMat 123) (codeMat 236) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit164_lb16_wc

theorem plane471GenSource0037 :
    QuotientRankAtLeast (spanCodes [272, 147, 82, 49, 10, 6]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 160, 68, 20, 10, 1] [(272, 440), (147, 434), (82, 422), (49, 68), (10, 262), (6, 1)]
    (codeMat 161) (codeMat 500) (codeMat 94) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit75_lb16_wc

theorem plane471GenSource0038 :
    QuotientRankAtLeast (spanCodes [262, 130, 84, 39, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 132, 32, 10, 1] [(262, 316), (130, 32), (84, 311), (39, 441), (10, 440)]
    (codeMat 379) (codeMat 340) (codeMat 85) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit196_lb16_unconditional

theorem plane471GenSource0039 :
    QuotientRankAtLeast (spanCodes [256, 132, 84, 33, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [276, 132, 96, 10, 1] [(256, 1), (132, 10), (84, 142), (33, 97), (10, 276)]
    (codeMat 396) (codeMat 84) (codeMat 84) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit213_lb16_wc

end QiushiMatmul
