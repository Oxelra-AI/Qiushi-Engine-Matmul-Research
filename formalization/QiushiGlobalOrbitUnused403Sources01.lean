import QiushiGlobalOrbitUnused403Data
import QiushiCertifiedTransport
import QiushiOrbit10FP
import QiushiWcOrbit218Dispatch
import QiushiWcOrbit238Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane403UnusedGenSource0010 :
    QuotientRankAtLeast (spanCodes [259, 146, 68, 51, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [294, 136, 96, 20, 1] [(259, 232), (146, 1), (68, 430), (51, 252), (10, 295)]
    (codeMat 183) (codeMat 107) (codeMat 428) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit238_lb16_wc

theorem plane403UnusedGenSource0011 :
    QuotientRankAtLeast (spanCodes [262, 151, 68, 54, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [310, 132, 96, 10, 1] [(262, 133), (151, 238), (68, 466), (54, 1), (10, 97)]
    (codeMat 163) (codeMat 459) (codeMat 346) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit218_lb16_wc

theorem plane403UnusedGenSource0012 :
    QuotientRankAtLeast (spanCodes [263, 150, 68, 55, 10]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [294, 136, 96, 20, 1] [(263, 463), (150, 294), (68, 430), (55, 475), (10, 137)]
    (codeMat 230) (codeMat 313) (codeMat 313) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit238_lb16_wc

theorem plane403UnusedGenSource0013 :
    QuotientRankAtLeast (spanCodes [288, 160, 68, 16, 8, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(288, 256), (160, 176), (68, 76), (16, 16), (8, 8), (2, 2), (1, 1)]
    (codeMat 401) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane403UnusedGenSource0014 :
    QuotientRankAtLeast (spanCodes [256, 144, 64, 48, 10, 4, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(256, 16), (144, 432), (64, 2), (48, 256), (10, 76), (4, 8), (1, 1)]
    (codeMat 161) (codeMat 177) (codeMat 417) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane403UnusedGenSource0015 :
    QuotientRankAtLeast (spanCodes [272, 128, 66, 32, 10, 6, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(272, 160), (128, 432), (66, 78), (32, 256), (10, 76), (6, 8), (1, 1)]
    (codeMat 177) (codeMat 401) (codeMat 401) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

end QiushiMatmul
