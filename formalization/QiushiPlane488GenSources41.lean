import QiushiPlane488GenData
import QiushiCertifiedTransport
import QiushiFlattenSeeds
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane488GenSource0410 :
    QuotientRankAtLeast (spanCodes [258, 128, 64, 32, 18, 10, 6, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(258, 197), (128, 3), (64, 2), (32, 40), (18, 216), (10, 208), (6, 384), (1, 128)]
    (codeMat 84) (codeMat 286) (codeMat 303) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

theorem plane488GenSource0411 :
    QuotientRankAtLeast (spanCodes [258, 130, 64, 32, 18, 10, 4, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(258, 452), (130, 455), (64, 2), (32, 32), (18, 504), (10, 464), (4, 256), (1, 128)]
    (codeMat 84) (codeMat 410) (codeMat 331) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

theorem plane488GenSource0412 :
    QuotientRankAtLeast (spanCodes [260, 128, 68, 36, 20, 8, 2, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(260, 455), (128, 2), (68, 452), (36, 504), (20, 464), (8, 32), (2, 128), (1, 256)]
    (codeMat 84) (codeMat 372) (codeMat 93) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

end QiushiMatmul
