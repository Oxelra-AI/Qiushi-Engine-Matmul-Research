import QiushiPlane427GenData
import QiushiCertifiedTransport
import QiushiFlattenSeeds
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane427GenSource0230 :
    QuotientRankAtLeast (spanCodes [258, 128, 64, 34, 16, 10, 6, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(258, 71), (128, 1), (64, 2), (34, 120), (16, 8), (10, 80), (6, 384), (1, 128)]
    (codeMat 84) (codeMat 302) (codeMat 302) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

theorem plane427GenSource0231 :
    QuotientRankAtLeast (spanCodes [256, 130, 66, 34, 16, 8, 6, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(256, 3), (130, 325), (66, 324), (34, 344), (16, 40), (8, 32), (6, 384), (1, 256)]
    (codeMat 84) (codeMat 230) (codeMat 159) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

theorem plane427GenSource0232 :
    QuotientRankAtLeast (spanCodes [258, 128, 66, 34, 16, 8, 6, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(258, 71), (128, 1), (66, 68), (34, 120), (16, 8), (8, 32), (6, 384), (1, 256)]
    (codeMat 84) (codeMat 358) (codeMat 158) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

theorem plane427GenSource0233 :
    QuotientRankAtLeast (spanCodes [258, 128, 66, 32, 16, 10, 4, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(258, 68), (128, 1), (66, 70), (32, 32), (16, 8), (10, 112), (4, 256), (1, 384)]
    (codeMat 84) (codeMat 330) (codeMat 394) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

theorem plane427GenSource0234 :
    QuotientRankAtLeast (spanCodes [258, 130, 64, 32, 16, 10, 4, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(258, 324), (130, 325), (64, 2), (32, 32), (16, 40), (10, 336), (4, 256), (1, 128)]
    (codeMat 84) (codeMat 394) (codeMat 330) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

theorem plane427GenSource0235 :
    QuotientRankAtLeast (spanCodes [256, 132, 68, 36, 16, 12, 2, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(256, 3), (132, 196), (68, 198), (36, 216), (16, 32), (12, 240), (2, 256), (1, 384)]
    (codeMat 84) (codeMat 236) (codeMat 123) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

theorem plane427GenSource0236 :
    QuotientRankAtLeast (spanCodes [260, 132, 64, 36, 16, 12, 2, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(260, 455), (132, 452), (64, 2), (36, 504), (16, 32), (12, 464), (2, 256), (1, 128)]
    (codeMat 84) (codeMat 428) (codeMat 107) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

end QiushiMatmul
