import QiushiPlane274GenData
import QiushiCertifiedTransport
import QiushiFlattenSeeds
import QiushiOrbit11FP
import QiushiOrbit13FP
import QiushiOrbit14FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane274GenSource0020 :
    QuotientRankAtLeast (spanCodes [260, 140, 76, 44, 28, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(260, 384), (140, 156), (76, 30), (44, 363), (28, 148), (2, 1), (1, 3)]
    (codeMat 369) (codeMat 299) (codeMat 318) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane274GenSource0021 :
    QuotientRankAtLeast (spanCodes [268, 136, 76, 40, 28, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(268, 182), (136, 69), (76, 52), (40, 128), (28, 112), (2, 40), (1, 32)]
    (codeMat 142) (codeMat 482) (codeMat 143) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane274GenSource0022 :
    QuotientRankAtLeast (spanCodes [268, 128, 68, 32, 20, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 68, 160, 256] [(268, 228), (128, 8), (68, 28), (32, 256), (20, 68), (2, 1), (1, 3)]
    (codeMat 161) (codeMat 267) (codeMat 282) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit13_lb12

theorem plane274GenSource0023 :
    QuotientRankAtLeast (spanCodes [256, 128, 76, 32, 28, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 1), (128, 2), (76, 118), (32, 8), (28, 96), (2, 128), (1, 384)]
    (codeMat 84) (codeMat 92) (codeMat 116) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane274GenSource0024 :
    QuotientRankAtLeast (spanCodes [256, 132, 68, 36, 20, 8, 2, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(256, 3), (132, 198), (68, 196), (36, 216), (20, 240), (8, 32), (2, 384), (1, 256)]
    (codeMat 84) (codeMat 244) (codeMat 95) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

theorem plane274GenSource0025 :
    QuotientRankAtLeast (spanCodes [256, 128, 68, 32, 20, 12, 2, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(256, 1), (128, 2), (68, 70), (32, 8), (20, 80), (12, 112), (2, 128), (1, 384)]
    (codeMat 84) (codeMat 92) (codeMat 116) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

theorem plane274GenSource0026 :
    QuotientRankAtLeast (spanCodes [260, 128, 68, 32, 20, 12, 2, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(260, 325), (128, 2), (68, 326), (32, 40), (20, 336), (12, 368), (2, 128), (1, 384)]
    (codeMat 84) (codeMat 348) (codeMat 125) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

theorem plane274GenSource0027 :
    QuotientRankAtLeast (spanCodes [260, 132, 68, 36, 20, 8, 2, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(260, 455), (132, 454), (68, 452), (36, 504), (20, 496), (8, 32), (2, 384), (1, 256)]
    (codeMat 84) (codeMat 500) (codeMat 94) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

theorem plane274GenSource0028 :
    QuotientRankAtLeast (spanCodes [256, 128, 68, 32, 20, 8, 2, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(256, 1), (128, 2), (68, 68), (32, 8), (20, 80), (8, 32), (2, 128), (1, 256)]
    (codeMat 84) (codeMat 84) (codeMat 84) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

end QiushiMatmul
