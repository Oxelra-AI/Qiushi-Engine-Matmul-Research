import QiushiPlane278GenData
import QiushiCertifiedTransport
import QiushiFlattenSeeds
import QiushiOrbit25FP
import QiushiOrbit35FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane278GenSource0020 :
    QuotientRankAtLeast (spanCodes [264, 88, 56, 4, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 4, 8, 80, 256] [(264, 80), (88, 344), (56, 256), (4, 2), (2, 5), (1, 3)]
    (codeMat 177) (codeMat 171) (codeMat 485) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit25_lb12

theorem plane278GenSource0021 :
    QuotientRankAtLeast (spanCodes [256, 132, 64, 32, 16, 12, 2, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(256, 1), (132, 68), (64, 2), (32, 8), (16, 32), (12, 80), (2, 256), (1, 128)]
    (codeMat 84) (codeMat 140) (codeMat 98) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

theorem plane278GenSource0022 :
    QuotientRankAtLeast (spanCodes [260, 132, 64, 32, 20, 12, 2, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(260, 325), (132, 326), (64, 2), (32, 40), (20, 368), (12, 336), (2, 384), (1, 128)]
    (codeMat 84) (codeMat 412) (codeMat 111) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

theorem plane278GenSource0023 :
    QuotientRankAtLeast (spanCodes [260, 132, 68, 36, 16, 12, 2, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(260, 455), (132, 452), (68, 454), (36, 504), (16, 32), (12, 496), (2, 256), (1, 384)]
    (codeMat 84) (codeMat 492) (codeMat 115) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

theorem plane278GenSource0024 :
    QuotientRankAtLeast (spanCodes [256, 128, 68, 36, 20, 12, 2, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(256, 3), (128, 2), (68, 198), (36, 216), (20, 208), (12, 240), (2, 128), (1, 384)]
    (codeMat 84) (codeMat 124) (codeMat 124) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

theorem plane278GenSource0025 :
    QuotientRankAtLeast (spanCodes [256, 128, 64, 32, 16, 8, 2, 1]) 3 := by
  apply quotientRankAtLeast_weaken (n := 3) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [128, 64, 32, 16, 8, 4, 2, 1] [(256, 4), (128, 1), (64, 2), (32, 32), (16, 8), (8, 16), (2, 64), (1, 128)]
    (codeMat 84) (codeMat 266) (codeMat 266) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_1

theorem plane278GenSource0026 :
    QuotientRankAtLeast (spanCodes [276, 68, 36, 8, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(276, 246), (68, 22), (36, 9), (8, 3), (2, 128), (1, 2)]
    (codeMat 267) (codeMat 165) (codeMat 163) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane278GenSource0027 :
    QuotientRankAtLeast (spanCodes [264, 128, 64, 32, 24, 2, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 96, 16, 8, 4, 2, 1] [(264, 100), (128, 8), (64, 9), (32, 256), (24, 4), (2, 16), (1, 18)]
    (codeMat 140) (codeMat 281) (codeMat 281) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_7

end QiushiMatmul
