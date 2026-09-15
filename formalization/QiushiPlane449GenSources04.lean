import QiushiPlane449GenData
import QiushiCertifiedTransport
import QiushiMonoOrbit149From65
import QiushiMonoOrbit311From196
import QiushiMonoOrbit340From196
import QiushiStep99Orbit196Dispatch
import QiushiStep99Orbit217Dispatch
import QiushiWcOrbit164Dispatch
import QiushiWcOrbit212Dispatch
import QiushiWcOrbit213Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane449GenSource0040 :
    QuotientRankAtLeast (spanCodes [276, 136, 68, 40, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 96, 20, 10, 1] [(276, 362), (136, 20), (68, 352), (40, 1), (1, 256)]
    (codeMat 98) (codeMat 340) (codeMat 85) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit164_lb16_wc

theorem plane449GenSource0041 :
    QuotientRankAtLeast (spanCodes [270, 146, 66, 50, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 132, 32, 10, 1] [(270, 142), (146, 32), (66, 11), (50, 440), (1, 1)]
    (codeMat 489) (codeMat 273) (codeMat 273) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit196_lb16_unconditional

theorem plane449GenSource0042 :
    QuotientRankAtLeast (spanCodes [264, 148, 70, 52, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [276, 132, 96, 10, 1] [(264, 132), (148, 496), (70, 10), (52, 96), (1, 1)]
    (codeMat 161) (codeMat 401) (codeMat 401) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit213_lb16_wc

theorem plane449GenSource0043 :
    QuotientRankAtLeast (spanCodes [266, 150, 66, 54, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [308, 132, 96, 10, 1] [(266, 107), (150, 132), (66, 10), (54, 432), (1, 1)]
    (codeMat 481) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit217_lb16_unconditional

theorem plane449GenSource0044 :
    QuotientRankAtLeast (spanCodes [264, 148, 66, 52, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [274, 132, 96, 10, 1] [(264, 96), (148, 133), (66, 10), (52, 509), (1, 1)]
    (codeMat 417) (codeMat 277) (codeMat 277) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit212_lb16_wc

theorem plane449GenSource0045 :
    QuotientRankAtLeast (spanCodes [316, 160, 122, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [384, 96, 10, 1] [(316, 11), (160, 490), (122, 107), (1, 384)]
    (codeMat 111) (codeMat 250) (codeMat 397) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit311_lb16_mono

theorem plane449GenSource0046 :
    QuotientRankAtLeast (spanCodes [316, 160, 124, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [258, 100, 16, 1] [(316, 374), (160, 101), (124, 375), (1, 16)]
    (codeMat 396) (codeMat 188) (codeMat 103) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit340_lb16_mono

theorem plane449GenSource0047 :
    QuotientRankAtLeast (spanCodes [256, 156, 66, 60, 1]) 16 := by
  apply quotientRankAtLeast_weaken (n := 16) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [278, 132, 32, 10, 1] [(256, 32), (156, 142), (66, 11), (60, 434), (1, 1)]
    (codeMat 481) (codeMat 275) (codeMat 275) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit196_lb16_unconditional

theorem plane449GenSource0048 :
    QuotientRankAtLeast (spanCodes [272, 128, 32, 12, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 68, 16, 10, 1] [(272, 10), (128, 16), (32, 1), (12, 68), (1, 256)]
    (codeMat 98) (codeMat 84) (codeMat 84) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit149_lb15_mono

theorem plane449GenSource0049 :
    QuotientRankAtLeast (spanCodes [284, 128, 66, 32, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 68, 16, 10, 1] [(284, 10), (128, 325), (66, 68), (32, 16), (1, 256)]
    (codeMat 85) (codeMat 226) (codeMat 141) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit149_lb15_mono

end QiushiMatmul
