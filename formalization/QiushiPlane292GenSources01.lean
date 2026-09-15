import QiushiPlane292GenData
import QiushiCertifiedTransport
import QiushiMonoOrbit169From76
import QiushiMonoOrbit188From76
import QiushiMonoOrbit192From65
import QiushiMonoOrbit193From69
import QiushiStep128Mono189From80T
import QiushiStep128Mono190From72
import QiushiStep98Orbit153Mono
import QiushiWcOrbit187Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane292GenSource0010 :
    QuotientRankAtLeast (spanCodes [272, 128, 32, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 96, 16, 10, 1] [(272, 10), (128, 1), (32, 16), (10, 96), (1, 256)]
    (codeMat 84) (codeMat 98) (codeMat 140) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step98_orbit153_lb15_unconditional

theorem plane292GenSource0011 :
    QuotientRankAtLeast (spanCodes [274, 128, 32, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [274, 128, 32, 10, 1] [(274, 274), (128, 128), (32, 32), (10, 10), (1, 1)]
    (codeMat 273) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit188_lb15_mono

theorem plane292GenSource0012 :
    QuotientRankAtLeast (spanCodes [276, 128, 32, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [288, 128, 20, 10, 1] [(276, 10), (128, 128), (32, 1), (10, 148), (1, 288)]
    (codeMat 298) (codeMat 84) (codeMat 84) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit169_lb15_mono

theorem plane292GenSource0013 :
    QuotientRankAtLeast (spanCodes [278, 128, 32, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 128, 32, 10, 1] [(278, 278), (128, 128), (32, 32), (10, 10), (1, 1)]
    (codeMat 273) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit189_lb15_mono

theorem plane292GenSource0014 :
    QuotientRankAtLeast (spanCodes [322, 128, 32, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [262, 128, 32, 10, 1] [(322, 10), (128, 1), (32, 390), (10, 268), (1, 32)]
    (codeMat 396) (codeMat 354) (codeMat 142) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit187_lb15_wc

theorem plane292GenSource0015 :
    QuotientRankAtLeast (spanCodes [324, 128, 32, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [324, 128, 32, 10, 1] [(324, 324), (128, 128), (32, 32), (10, 10), (1, 1)]
    (codeMat 273) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit190_lb15_mono

theorem plane292GenSource0016 :
    QuotientRankAtLeast (spanCodes [336, 128, 32, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [288, 128, 20, 10, 1] [(336, 10), (128, 1), (32, 128), (10, 148), (1, 288)]
    (codeMat 84) (codeMat 330) (codeMat 394) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit169_lb15_mono

theorem plane292GenSource0017 :
    QuotientRankAtLeast (spanCodes [338, 128, 32, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 128, 32, 10, 1] [(338, 284), (128, 32), (32, 128), (10, 10), (1, 1)]
    (codeMat 273) (codeMat 273) (codeMat 273) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit189_lb15_mono

theorem plane292GenSource0018 :
    QuotientRankAtLeast (spanCodes [340, 128, 32, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [340, 128, 32, 10, 1] [(340, 340), (128, 128), (32, 32), (10, 10), (1, 1)]
    (codeMat 273) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit192_lb15_mono

theorem plane292GenSource0019 :
    QuotientRankAtLeast (spanCodes [342, 128, 32, 10, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [342, 128, 32, 10, 1] [(342, 342), (128, 128), (32, 32), (10, 10), (1, 1)]
    (codeMat 273) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit193_lb15_mono

end QiushiMatmul
