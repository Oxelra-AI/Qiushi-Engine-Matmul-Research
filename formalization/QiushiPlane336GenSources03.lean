import QiushiPlane336GenData
import QiushiCertifiedTransport
import QiushiFlattenSeeds
import QiushiOrbit5FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane336GenSource0030 :
    QuotientRankAtLeast (spanCodes [256, 128, 64, 34, 16, 8, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 4, 8, 16, 64, 160] [(256, 4), (128, 2), (64, 1), (34, 160), (16, 16), (8, 8), (1, 64)]
    (codeMat 84) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit5_lb9

theorem plane336GenSource0031 :
    QuotientRankAtLeast (spanCodes [256, 130, 64, 34, 16, 10, 6, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(256, 3), (130, 325), (64, 2), (34, 344), (16, 40), (10, 336), (6, 384), (1, 128)]
    (codeMat 84) (codeMat 174) (codeMat 359) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

theorem plane336GenSource0032 :
    QuotientRankAtLeast (spanCodes [256, 130, 66, 32, 16, 10, 6, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(256, 1), (130, 325), (66, 326), (32, 8), (16, 40), (10, 368), (6, 256), (1, 384)]
    (codeMat 84) (codeMat 206) (codeMat 498) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

theorem plane336GenSource0033 :
    QuotientRankAtLeast (spanCodes [256, 132, 68, 36, 16, 12, 2, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(256, 3), (132, 196), (68, 198), (36, 216), (16, 32), (12, 240), (2, 256), (1, 384)]
    (codeMat 84) (codeMat 236) (codeMat 123) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

end QiushiMatmul
