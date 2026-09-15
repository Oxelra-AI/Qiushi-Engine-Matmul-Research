import QiushiPlane298GenData
import QiushiCertifiedTransport
import QiushiMonoOrbit151From65
import QiushiMonoOrbit169From76
import QiushiMonoOrbit177From69
import QiushiMonoOrbit188From76
import QiushiStep128Mono158From72
import QiushiStep128Mono189From80T
import QiushiStep98Orbit153Mono
import QiushiWcOrbit183Dispatch
import QiushiWcOrbit185Dispatch
import QiushiWcOrbit187Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane298GenSource0000 :
    QuotientRankAtLeast (spanCodes [384, 32, 20, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [192, 32, 20, 10, 1] [(384, 192), (32, 1), (20, 10), (10, 20), (1, 32)]
    (codeMat 266) (codeMat 84) (codeMat 84) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit158_lb15_mono

theorem plane298GenSource0001 :
    QuotientRankAtLeast (spanCodes [384, 68, 32, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [144, 68, 32, 10, 1] [(384, 32), (68, 10), (32, 144), (10, 78), (1, 1)]
    (codeMat 417) (codeMat 177) (codeMat 417) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit177_lb15_mono

theorem plane298GenSource0002 :
    QuotientRankAtLeast (spanCodes [384, 70, 32, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [288, 68, 16, 10, 1] [(384, 16), (70, 10), (32, 288), (10, 78), (1, 1)]
    (codeMat 417) (codeMat 401) (codeMat 401) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit151_lb15_mono

theorem plane298GenSource0003 :
    QuotientRankAtLeast (spanCodes [384, 80, 32, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [288, 128, 20, 10, 1] [(384, 288), (80, 20), (32, 128), (10, 10), (1, 1)]
    (codeMat 273) (codeMat 273) (codeMat 273) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit169_lb15_mono

theorem plane298GenSource0004 :
    QuotientRankAtLeast (spanCodes [384, 84, 32, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [384, 84, 32, 10, 1] [(384, 384), (84, 84), (32, 32), (10, 10), (1, 1)]
    (codeMat 273) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit183_lb15_wc

theorem plane298GenSource0005 :
    QuotientRankAtLeast (spanCodes [384, 86, 32, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [400, 84, 32, 10, 1] [(384, 432), (86, 94), (32, 32), (10, 10), (1, 1)]
    (codeMat 401) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit185_lb15_wc

theorem plane298GenSource0006 :
    QuotientRankAtLeast (spanCodes [258, 130, 32, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 32, 10, 1] [(258, 262), (130, 128), (32, 32), (10, 10), (1, 1)]
    (codeMat 337) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit187_lb15_wc

theorem plane298GenSource0007 :
    QuotientRankAtLeast (spanCodes [262, 134, 32, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [274, 128, 32, 10, 1] [(262, 10), (134, 11), (32, 128), (10, 280), (1, 32)]
    (codeMat 140) (codeMat 114) (codeMat 204) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit188_lb15_mono

theorem plane298GenSource0008 :
    QuotientRankAtLeast (spanCodes [272, 144, 32, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 96, 16, 10, 1] [(272, 26), (144, 1), (32, 16), (10, 96), (1, 256)]
    (codeMat 86) (codeMat 98) (codeMat 140) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step98_orbit153_lb15_unconditional

theorem plane298GenSource0009 :
    QuotientRankAtLeast (spanCodes [274, 146, 32, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 128, 32, 10, 1] [(274, 310), (146, 128), (32, 32), (10, 10), (1, 1)]
    (codeMat 465) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit189_lb15_mono

end QiushiMatmul
