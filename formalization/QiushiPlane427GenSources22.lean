import QiushiPlane427GenData
import QiushiCertifiedTransport
import QiushiFlattenSeeds
import QiushiOrbit11FP
import QiushiOrbit14FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane427GenSource0220 :
    QuotientRankAtLeast (spanCodes [386, 66, 34, 16, 8, 6, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(386, 197), (66, 69), (34, 53), (16, 40), (8, 8), (6, 3), (1, 1)]
    (codeMat 273) (codeMat 419) (codeMat 183) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane427GenSource0221 :
    QuotientRankAtLeast (spanCodes [258, 194, 32, 16, 10, 4, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(258, 112), (194, 240), (32, 9), (16, 54), (10, 29), (4, 8), (1, 40)]
    (codeMat 267) (codeMat 213) (codeMat 470) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane427GenSource0222 :
    QuotientRankAtLeast (spanCodes [264, 132, 64, 36, 16, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(264, 97), (132, 20), (64, 8), (36, 256), (16, 130), (2, 2), (1, 1)]
    (codeMat 225) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane427GenSource0223 :
    QuotientRankAtLeast (spanCodes [324, 132, 36, 16, 12, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(324, 240), (132, 112), (36, 54), (16, 1), (12, 53), (2, 8), (1, 40)]
    (codeMat 266) (codeMat 355) (codeMat 190) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane427GenSource0224 :
    QuotientRankAtLeast (spanCodes [256, 132, 64, 36, 16, 12, 2, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(256, 3), (132, 196), (64, 2), (36, 216), (16, 32), (12, 208), (2, 256), (1, 128)]
    (codeMat 84) (codeMat 172) (codeMat 99) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

theorem plane427GenSource0225 :
    QuotientRankAtLeast (spanCodes [260, 132, 68, 36, 16, 12, 2, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(260, 455), (132, 452), (68, 454), (36, 504), (16, 32), (12, 496), (2, 256), (1, 384)]
    (codeMat 84) (codeMat 492) (codeMat 115) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

theorem plane427GenSource0226 :
    QuotientRankAtLeast (spanCodes [258, 128, 64, 32, 16, 10, 4, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(258, 68), (128, 1), (64, 2), (32, 32), (16, 8), (10, 80), (4, 256), (1, 128)]
    (codeMat 84) (codeMat 266) (codeMat 266) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

theorem plane427GenSource0227 :
    QuotientRankAtLeast (spanCodes [258, 130, 66, 32, 16, 10, 4, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(258, 324), (130, 325), (66, 326), (32, 32), (16, 40), (10, 368), (4, 256), (1, 384)]
    (codeMat 84) (codeMat 458) (codeMat 458) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

theorem plane427GenSource0228 :
    QuotientRankAtLeast (spanCodes [256, 128, 66, 34, 16, 8, 6, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(256, 3), (128, 1), (66, 68), (34, 88), (16, 8), (8, 32), (6, 128), (1, 256)]
    (codeMat 84) (codeMat 102) (codeMat 156) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

theorem plane427GenSource0229 :
    QuotientRankAtLeast (spanCodes [258, 130, 66, 34, 16, 8, 6, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(258, 327), (130, 325), (66, 324), (34, 376), (16, 40), (8, 32), (6, 128), (1, 256)]
    (codeMat 84) (codeMat 486) (codeMat 157) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

end QiushiMatmul
