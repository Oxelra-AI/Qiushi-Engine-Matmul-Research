import QiushiGlobalOrbitUnused309Data
import QiushiCertifiedTransport
import QiushiFlattenSeeds
import QiushiOrbit11FP
import QiushiOrbit14FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane309UnusedGenSource0020 :
    QuotientRankAtLeast (spanCodes [272, 146, 82, 50, 10, 6, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(272, 406), (146, 256), (82, 255), (50, 20), (10, 28), (6, 2), (1, 3)]
    (codeMat 465) (codeMat 425) (codeMat 249) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane309UnusedGenSource0021 :
    QuotientRankAtLeast (spanCodes [258, 128, 64, 32, 16, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(258, 68), (128, 1), (64, 2), (32, 32), (16, 8), (10, 80), (1, 128)]
    (codeMat 84) (codeMat 266) (codeMat 266) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane309UnusedGenSource0022 :
    QuotientRankAtLeast (spanCodes [256, 128, 66, 34, 16, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(256, 54), (128, 9), (66, 82), (34, 112), (16, 8), (10, 80), (1, 128)]
    (codeMat 86) (codeMat 298) (codeMat 270) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane309UnusedGenSource0023 :
    QuotientRankAtLeast (spanCodes [258, 130, 64, 32, 20, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(258, 139), (130, 9), (64, 2), (32, 360), (20, 245), (10, 30), (1, 3)]
    (codeMat 485) (codeMat 307) (codeMat 311) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane309UnusedGenSource0024 :
    QuotientRankAtLeast (spanCodes [256, 134, 66, 34, 20, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 511), (134, 255), (66, 28), (34, 374), (20, 246), (10, 30), (1, 3)]
    (codeMat 375) (codeMat 311) (codeMat 307) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane309UnusedGenSource0025 :
    QuotientRankAtLeast (spanCodes [258, 130, 64, 32, 22, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(258, 136), (130, 8), (64, 2), (32, 360), (22, 232), (10, 29), (1, 3)]
    (codeMat 485) (codeMat 305) (codeMat 305) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane309UnusedGenSource0026 :
    QuotientRankAtLeast (spanCodes [258, 130, 64, 32, 18, 10, 4, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(258, 69), (130, 325), (64, 32), (32, 3), (18, 130), (10, 89), (4, 1), (1, 8)]
    (codeMat 281) (codeMat 142) (codeMat 354) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

theorem plane309UnusedGenSource0027 :
    QuotientRankAtLeast (spanCodes [256, 128, 66, 34, 18, 10, 4, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(256, 32), (128, 256), (66, 100), (34, 88), (18, 128), (10, 91), (4, 8), (1, 9)]
    (codeMat 281) (codeMat 169) (codeMat 225) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

end QiushiMatmul
