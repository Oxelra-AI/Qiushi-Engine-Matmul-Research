import QiushiPlane338GenData
import QiushiCertifiedTransport
import QiushiMonoOrbit192From65
import QiushiMonoOrbit209From65
import QiushiStep98Orbit153Mono
import QiushiWcOrbit180Dispatch
import QiushiWcOrbit185Dispatch
import QiushiWcOrbit197Dispatch
import QiushiWcOrbit220Dispatch
import QiushiWcOrbit233Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane338GenSource0000 :
    QuotientRankAtLeast (spanCodes [288, 98, 16, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 96, 16, 10, 1] [(288, 256), (98, 106), (16, 16), (10, 10), (1, 1)]
    (codeMat 401) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step98_orbit153_lb15_unconditional

theorem plane338GenSource0001 :
    QuotientRankAtLeast (spanCodes [288, 98, 16, 12, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [144, 84, 32, 10, 1] [(288, 144), (98, 84), (16, 32), (12, 10), (1, 1)]
    (codeMat 273) (codeMat 161) (codeMat 161) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit180_lb15_wc

theorem plane338GenSource0002 :
    QuotientRankAtLeast (spanCodes [288, 98, 16, 14, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [400, 84, 32, 10, 1] [(288, 432), (98, 116), (16, 32), (14, 10), (1, 1)]
    (codeMat 273) (codeMat 417) (codeMat 177) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit185_lb15_wc

theorem plane338GenSource0003 :
    QuotientRankAtLeast (spanCodes [268, 78, 44, 16, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [324, 132, 32, 10, 1] [(268, 356), (78, 11), (44, 324), (16, 448), (1, 1)]
    (codeMat 177) (codeMat 403) (codeMat 403) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit197_lb15_wc

theorem plane338GenSource0004 :
    QuotientRankAtLeast (spanCodes [288, 132, 98, 16, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [340, 128, 32, 10, 1] [(288, 511), (132, 42), (98, 500), (16, 128), (1, 32)]
    (codeMat 141) (codeMat 372) (codeMat 93) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit192_lb15_mono

theorem plane338GenSource0005 :
    QuotientRankAtLeast (spanCodes [288, 134, 98, 16, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [334, 192, 36, 16, 1] [(288, 16), (134, 209), (98, 443), (16, 192), (1, 36)]
    (codeMat 183) (codeMat 114) (codeMat 204) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit220_lb15_wc

theorem plane338GenSource0006 :
    QuotientRankAtLeast (spanCodes [288, 136, 98, 16, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [144, 84, 32, 10, 1] [(288, 32), (136, 11), (98, 94), (16, 1), (1, 144)]
    (codeMat 498) (codeMat 266) (codeMat 266) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit180_lb15_wc

theorem plane338GenSource0007 :
    QuotientRankAtLeast (spanCodes [288, 138, 98, 16, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [400, 84, 32, 10, 1] [(288, 432), (138, 11), (98, 116), (16, 1), (1, 32)]
    (codeMat 122) (codeMat 298) (codeMat 270) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit185_lb15_wc

theorem plane338GenSource0008 :
    QuotientRankAtLeast (spanCodes [288, 140, 98, 16, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 140, 98, 16, 1] [(288, 260), (140, 98), (98, 140), (16, 1), (1, 16)]
    (codeMat 266) (codeMat 266) (codeMat 266) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit233_lb15_wc

theorem plane338GenSource0009 :
    QuotientRankAtLeast (spanCodes [288, 142, 98, 16, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [288, 160, 84, 10, 1] [(288, 1), (142, 468), (98, 254), (16, 288), (1, 384)]
    (codeMat 94) (codeMat 204) (codeMat 114) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit209_lb15_mono

end QiushiMatmul
