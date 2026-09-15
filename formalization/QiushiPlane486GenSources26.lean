import QiushiPlane486GenData
import QiushiCertifiedTransport
import QiushiFlattenSeeds
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane486GenSource0260 :
    QuotientRankAtLeast (spanCodes [260, 128, 68, 36, 20, 8, 2, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(260, 455), (128, 2), (68, 452), (36, 504), (20, 464), (8, 32), (2, 128), (1, 256)]
    (codeMat 84) (codeMat 372) (codeMat 93) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

theorem plane486GenSource0261 :
    QuotientRankAtLeast (spanCodes [256, 128, 64, 32, 8, 4, 2, 1]) 3 := by
  apply quotientRankAtLeast_weaken (n := 3) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [128, 64, 32, 16, 8, 4, 2, 1] [(256, 1), (128, 4), (64, 2), (32, 64), (8, 128), (4, 8), (2, 32), (1, 16)]
    (codeMat 140) (codeMat 140) (codeMat 98) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_1

end QiushiMatmul
