import QiushiPlane471LowerGenData
import QiushiCertifiedTransport
import QiushiMonoOrbit112From35T
import QiushiMonoOrbit320From196
import QiushiStep128Mono246From75
import QiushiWcOrbit164Dispatch
import QiushiWcOrbit214Dispatch
import QiushiWcOrbit238Dispatch
import QiushiWcOrbit239Dispatch
import QiushiWcOrbit242Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane471LowerGenSource0040 :
    QuotientRankAtLeast (spanCodes [289, 167, 84, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [304, 160, 10, 1] [(289, 170), (167, 171), (84, 161), (10, 411)]
    (codeMat 253) (codeMat 501) (codeMat 494) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit320_lb16_mono

theorem plane471LowerGenSource0041 :
    QuotientRankAtLeast (spanCodes [272, 129, 84, 49, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 164, 68, 19, 10] [(272, 25), (129, 507), (84, 87), (49, 488), (10, 224)]
    (codeMat 212) (codeMat 95) (codeMat 244) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit242_lb16_wc

theorem plane471LowerGenSource0042 :
    QuotientRankAtLeast (spanCodes [272, 128, 84, 49, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 132, 96, 10, 1] [(272, 10), (128, 1), (84, 142), (49, 284), (10, 97)]
    (codeMat 340) (codeMat 98) (codeMat 140) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit214_lb16_wc

theorem plane471LowerGenSource0043 :
    QuotientRankAtLeast (spanCodes [274, 129, 84, 51, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [294, 136, 96, 20, 1] [(274, 252), (129, 96), (84, 157), (51, 430), (10, 232)]
    (codeMat 309) (codeMat 244) (codeMat 95) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit238_lb16_wc

theorem plane471LowerGenSource0044 :
    QuotientRankAtLeast (spanCodes [275, 129, 84, 50, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [294, 136, 96, 20, 1] [(275, 442), (129, 338), (84, 253), (50, 136), (10, 137)]
    (codeMat 394) (codeMat 425) (codeMat 249) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit238_lb16_wc

theorem plane471LowerGenSource0045 :
    QuotientRankAtLeast (spanCodes [278, 131, 84, 55, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 160, 68, 19, 10] [(278, 19), (131, 322), (84, 277), (55, 328), (10, 488)]
    (codeMat 93) (codeMat 117) (codeMat 380) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit239_lb16_wc

theorem plane471LowerGenSource0046 :
    QuotientRankAtLeast (spanCodes [289, 181, 84, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [304, 160, 10, 1] [(289, 170), (181, 401), (84, 314), (10, 411)]
    (codeMat 188) (codeMat 375) (codeMat 491) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit320_lb16_mono

theorem plane471LowerGenSource0047 :
    QuotientRankAtLeast (spanCodes [278, 129, 84, 55, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [259, 162, 68, 20, 10] [(278, 248), (129, 10), (84, 230), (55, 497), (10, 90)]
    (codeMat 428) (codeMat 275) (codeMat 275) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit246_lb16_mono

theorem plane471LowerGenSource0048 :
    QuotientRankAtLeast (spanCodes [278, 128, 84, 55, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 96, 20, 10, 1] [(278, 276), (128, 256), (84, 372), (55, 126), (10, 287)]
    (codeMat 303) (codeMat 233) (codeMat 233) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit164_lb16_wc

theorem plane471LowerGenSource0049 :
    QuotientRankAtLeast (spanCodes [288, 80, 10, 4, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 96, 8, 2, 1] [(288, 2), (80, 272), (10, 104), (4, 1), (1, 8)]
    (codeMat 177) (codeMat 156) (codeMat 102) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit112_lb15_mono

end QiushiMatmul
