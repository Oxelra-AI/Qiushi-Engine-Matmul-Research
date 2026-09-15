import QiushiPlane462GenData
import QiushiCertifiedTransport
import QiushiFlattenSeeds
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane462GenSource0290 :
    QuotientRankAtLeast (spanCodes [258, 130, 64, 34, 18, 10, 4, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(258, 454), (130, 455), (64, 2), (34, 496), (18, 504), (10, 464), (4, 384), (1, 128)]
    (codeMat 84) (codeMat 442) (codeMat 334) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

theorem plane462GenSource0291 :
    QuotientRankAtLeast (spanCodes [258, 130, 64, 32, 16, 10, 4, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(258, 324), (130, 325), (64, 2), (32, 32), (16, 40), (10, 336), (4, 256), (1, 128)]
    (codeMat 84) (codeMat 394) (codeMat 330) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

theorem plane462GenSource0292 :
    QuotientRankAtLeast (spanCodes [260, 128, 68, 36, 20, 8, 2, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(260, 455), (128, 2), (68, 452), (36, 504), (20, 464), (8, 32), (2, 128), (1, 256)]
    (codeMat 84) (codeMat 372) (codeMat 93) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

theorem plane462GenSource0293 :
    QuotientRankAtLeast (spanCodes [256, 132, 68, 32, 20, 8, 2, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(256, 1), (132, 70), (68, 68), (32, 8), (20, 112), (8, 32), (2, 384), (1, 256)]
    (codeMat 84) (codeMat 212) (codeMat 86) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

end QiushiMatmul
