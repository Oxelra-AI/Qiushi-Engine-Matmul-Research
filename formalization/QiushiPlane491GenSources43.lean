import QiushiPlane491GenData
import QiushiCertifiedTransport
import QiushiMonoOrbit74From17
import QiushiOrbit29FP
import QiushiOrbit35FP
import QiushiStep99Orbit55Dispatch
import QiushiStep99Orbit65Dispatch
import QiushiStep99Orbit69Dispatch
import QiushiWcOrbit113Dispatch
import QiushiWcOrbit114Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane491GenSource0430 :
    QuotientRankAtLeast (spanCodes [265, 140, 77, 44, 25, 3]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(265, 246), (140, 124), (77, 29), (44, 232), (25, 96), (3, 8)]
    (codeMat 206) (codeMat 481) (codeMat 185) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane491GenSource0431 :
    QuotientRankAtLeast (spanCodes [272, 137, 81, 41, 5, 3]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160] [(272, 68), (137, 245), (81, 246), (41, 176), (5, 16), (3, 24)]
    (codeMat 142) (codeMat 458) (codeMat 458) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit29_lb15

theorem plane491GenSource0432 :
    QuotientRankAtLeast (spanCodes [269, 133, 64, 36, 20, 2]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [260, 160, 68, 16, 10, 1] [(269, 245), (133, 176), (64, 320), (36, 27), (20, 26), (2, 16)]
    (codeMat 266) (codeMat 117) (codeMat 380) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit65_lb15_unconditional

theorem plane491GenSource0433 :
    QuotientRankAtLeast (spanCodes [264, 133, 69, 36, 17, 2]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 164, 96, 16, 10, 1] [(264, 362), (133, 452), (69, 453), (36, 16), (17, 96), (2, 256)]
    (codeMat 92) (codeMat 225) (codeMat 169) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit69_lb15_unconditional

theorem plane491GenSource0434 :
    QuotientRankAtLeast (spanCodes [144, 84, 48, 2, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [384, 96, 8, 2, 1] [(144, 2), (84, 99), (48, 384), (2, 1), (1, 9)]
    (codeMat 305) (codeMat 271) (codeMat 314) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit113_lb14_wc

theorem plane491GenSource0435 :
    QuotientRankAtLeast (spanCodes [146, 84, 48, 8, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [384, 96, 8, 2, 1] [(146, 384), (84, 106), (48, 2), (8, 1), (1, 9)]
    (codeMat 474) (codeMat 401) (codeMat 401) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit113_lb14_wc

theorem plane491GenSource0436 :
    QuotientRankAtLeast (spanCodes [132, 69, 36, 17, 13, 3]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 132, 32, 12, 2, 1] [(132, 136), (69, 440), (36, 1), (17, 34), (13, 14), (3, 32)]
    (codeMat 267) (codeMat 92) (codeMat 116) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_orbit55_lb14_unconditional

theorem plane491GenSource0437 :
    QuotientRankAtLeast (spanCodes [130, 65, 33, 21, 9]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 160, 8, 2, 1] [(130, 2), (65, 1), (33, 264), (21, 416), (9, 8)]
    (codeMat 157) (codeMat 277) (codeMat 277) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit114_lb14_wc

theorem plane491GenSource0438 :
    QuotientRankAtLeast (spanCodes [131, 64, 32, 19, 10, 7]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [324, 192, 32, 20, 10, 1] [(131, 389), (64, 192), (32, 32), (19, 53), (10, 30), (7, 1)]
    (codeMat 273) (codeMat 409) (codeMat 473) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit74_lb14_mono

theorem plane491GenSource0439 :
    QuotientRankAtLeast (spanCodes [272, 144, 84, 48, 3]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 160, 8, 2, 1] [(272, 11), (144, 3), (84, 163), (48, 9), (3, 256)]
    (codeMat 102) (codeMat 123) (codeMat 236) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit114_lb14_wc

end QiushiMatmul
