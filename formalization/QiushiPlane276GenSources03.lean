import QiushiPlane276GenData
import QiushiCertifiedTransport
import QiushiFlattenSeeds
import QiushiOrbit35FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane276GenSource0030 :
    QuotientRankAtLeast (spanCodes [272, 144, 80, 48, 8, 2, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 32, 20, 8, 2, 1] [(272, 55), (144, 54), (80, 52), (48, 8), (8, 32), (2, 384), (1, 256)]
    (codeMat 84) (codeMat 500) (codeMat 94) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_12

theorem plane276GenSource0031 :
    QuotientRankAtLeast (spanCodes [272, 144, 80, 48, 8, 4, 2, 1]) 6 := by
  apply quotientRankAtLeast_weaken (n := 6) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 160, 64, 16, 8, 4, 2, 1] [(272, 496), (144, 504), (80, 480), (48, 64), (8, 256), (4, 6), (2, 7), (1, 4)]
    (codeMat 161) (codeMat 498) (codeMat 206) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_2

theorem plane276GenSource0032 :
    QuotientRankAtLeast (spanCodes [256, 136, 64, 32, 16, 4, 2, 1]) 6 := by
  apply quotientRankAtLeast_weaken (n := 6) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 160, 64, 16, 8, 4, 2, 1] [(256, 8), (136, 160), (64, 16), (32, 64), (16, 256), (4, 1), (2, 4), (1, 2)]
    (codeMat 161) (codeMat 140) (codeMat 98) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_2

theorem plane276GenSource0033 :
    QuotientRankAtLeast (spanCodes [264, 128, 72, 40, 24, 4, 2, 1]) 6 := by
  apply quotientRankAtLeast_weaken (n := 6) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 160, 64, 16, 8, 4, 2, 1] [(264, 496), (128, 16), (72, 504), (40, 64), (24, 320), (4, 6), (2, 2), (1, 7)]
    (codeMat 161) (codeMat 377) (codeMat 369) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_2

theorem plane276GenSource0034 :
    QuotientRankAtLeast (spanCodes [260, 128, 96, 20, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(260, 8), (128, 3), (96, 224), (20, 20), (2, 2), (1, 128)]
    (codeMat 141) (codeMat 98) (codeMat 140) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane276GenSource0035 :
    QuotientRankAtLeast (spanCodes [272, 68, 36, 8, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(272, 224), (68, 20), (36, 8), (8, 3), (2, 128), (1, 2)]
    (codeMat 267) (codeMat 161) (codeMat 161) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

theorem plane276GenSource0036 :
    QuotientRankAtLeast (spanCodes [268, 164, 96, 28, 2, 1]) 15 := by
  apply quotientRankAtLeast_weaken (n := 15) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128] [(268, 104), (164, 119), (96, 224), (28, 148), (2, 130), (1, 128)]
    (codeMat 143) (codeMat 482) (codeMat 143) true
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit35_lb15

end QiushiMatmul
