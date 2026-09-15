import QiushiPlane254GenData
import QiushiCertifiedTransport
import QiushiFlattenSeeds
import QiushiOrbit10FP
import QiushiOrbit25FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane254GenSource0020 :
    QuotientRankAtLeast (spanCodes [288, 164, 68, 16, 8, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(288, 325), (164, 237), (68, 168), (16, 3), (8, 2), (2, 24), (1, 16)]
    (codeMat 266) (codeMat 286) (codeMat 303) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane254GenSource0021 :
    QuotientRankAtLeast (spanCodes [416, 80, 8, 4, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 4, 8, 80, 256] [(416, 344), (80, 80), (8, 8), (4, 6), (2, 3), (1, 1)]
    (codeMat 401) (codeMat 307) (codeMat 311) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit25_lb12

theorem plane254GenSource0022 :
    QuotientRankAtLeast (spanCodes [256, 160, 68, 16, 8, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(256, 256), (160, 68), (68, 160), (16, 1), (8, 2), (2, 8), (1, 16)]
    (codeMat 266) (codeMat 266) (codeMat 266) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane254GenSource0023 :
    QuotientRankAtLeast (spanCodes [260, 160, 68, 16, 8, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(260, 432), (160, 70), (68, 176), (16, 1), (8, 2), (2, 8), (1, 16)]
    (codeMat 266) (codeMat 298) (codeMat 270) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane254GenSource0024 :
    QuotientRankAtLeast (spanCodes [432, 80, 8, 4, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 4, 8, 80, 256] [(432, 256), (80, 88), (8, 8), (4, 6), (2, 2), (1, 1)]
    (codeMat 401) (codeMat 305) (codeMat 305) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit25_lb12

theorem plane254GenSource0025 :
    QuotientRankAtLeast (spanCodes [288, 160, 64, 16, 8, 4, 2, 1]) 6 := by
  apply quotientRankAtLeast_weaken (n := 6) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 160, 64, 16, 8, 4, 2, 1] [(288, 432), (160, 416), (64, 8), (16, 256), (8, 64), (4, 6), (2, 4), (1, 1)]
    (codeMat 161) (codeMat 417) (codeMat 177) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_2

end QiushiMatmul
