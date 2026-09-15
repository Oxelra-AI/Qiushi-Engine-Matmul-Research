import QiushiPlane275GenData
import QiushiCertifiedTransport
import QiushiFlattenSeeds
import QiushiMonoOrbit142From56
import QiushiMonoOrbit43From14
import QiushiStep99Mono3032
import QiushiWcOrbit141Dispatch
import QiushiWcOrbit25Dispatch
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane275GenSource0020 :
    QuotientRankAtLeast (spanCodes [312, 160, 84, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [264, 84, 32, 2, 1] [(312, 119), (160, 350), (84, 85), (2, 3), (1, 2)]
    (codeMat 249) (codeMat 314) (codeMat 271) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit141_lb15_wc

theorem plane275GenSource0021 :
    QuotientRankAtLeast (spanCodes [316, 160, 84, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [264, 84, 32, 2, 1] [(316, 119), (160, 349), (84, 87), (2, 3), (1, 2)]
    (codeMat 241) (codeMat 314) (codeMat 271) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit141_lb15_wc

theorem plane275GenSource0022 :
    QuotientRankAtLeast (spanCodes [272, 160, 84, 2, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 84, 32, 2, 1] [(272, 272), (160, 304), (84, 86), (2, 2), (1, 3)]
    (codeMat 305) (codeMat 313) (codeMat 313) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit142_lb14_mono

theorem plane275GenSource0023 :
    QuotientRankAtLeast (spanCodes [292, 160, 84, 2, 1]) 14 := by
  apply quotientRankAtLeast_weaken (n := 14) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 84, 32, 2, 1] [(292, 325), (160, 356), (84, 87), (2, 1), (1, 3)]
    (codeMat 425) (codeMat 271) (codeMat 314) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit142_lb14_mono

theorem plane275GenSource0024 :
    QuotientRankAtLeast (spanCodes [140, 72, 44, 28, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 68, 16, 8, 2, 1] [(140, 86), (72, 24), (44, 326), (28, 70), (2, 2), (1, 3)]
    (codeMat 177) (codeMat 313) (codeMat 313) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_mono_30_lb12

theorem plane275GenSource0025 :
    QuotientRankAtLeast (spanCodes [128, 64, 32, 20, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 68, 16, 8, 2, 1] [(128, 8), (64, 16), (32, 256), (20, 68), (2, 1), (1, 2)]
    (codeMat 161) (codeMat 266) (codeMat 266) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step99_mono_30_lb12

theorem plane275GenSource0026 :
    QuotientRankAtLeast (spanCodes [276, 148, 84, 52, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [272, 128, 32, 8, 2, 1] [(276, 274), (148, 272), (84, 273), (52, 162), (2, 32), (1, 40)]
    (codeMat 460) (codeMat 481) (codeMat 185) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit43_lb12_mono

theorem plane275GenSource0027 :
    QuotientRankAtLeast (spanCodes [288, 160, 80, 4, 2, 1]) 11 := by
  apply quotientRankAtLeast_weaken (n := 11) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 80, 8, 4, 2, 1] [(288, 256), (160, 264), (80, 344), (4, 4), (2, 5), (1, 6)]
    (codeMat 417) (codeMat 458) (codeMat 458) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.step109_orbit25_lb11_wc

theorem plane275GenSource0028 :
    QuotientRankAtLeast (spanCodes [272, 128, 80, 32, 4, 2, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 96, 16, 8, 4, 2, 1] [(272, 96), (128, 8), (80, 112), (32, 256), (4, 4), (2, 1), (1, 6)]
    (codeMat 161) (codeMat 330) (codeMat 394) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_7

end QiushiMatmul
