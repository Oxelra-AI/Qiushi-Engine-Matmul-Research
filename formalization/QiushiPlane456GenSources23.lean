import QiushiPlane456GenData
import QiushiCertifiedTransport
import QiushiFlattenSeeds
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane456GenSource0230 :
    QuotientRankAtLeast (spanCodes [258, 128, 66, 32, 16, 10, 4, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(258, 68), (128, 1), (66, 70), (32, 32), (16, 8), (10, 112), (4, 256), (1, 384)]
    (codeMat 84) (codeMat 330) (codeMat 394) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

theorem plane456GenSource0231 :
    QuotientRankAtLeast (spanCodes [258, 130, 64, 34, 16, 10, 4, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(258, 326), (130, 325), (64, 2), (34, 368), (16, 40), (10, 336), (4, 384), (1, 128)]
    (codeMat 84) (codeMat 426) (codeMat 335) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

theorem plane456GenSource0232 :
    QuotientRankAtLeast (spanCodes [256, 130, 66, 34, 16, 10, 4, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(256, 2), (130, 325), (66, 326), (34, 336), (16, 40), (10, 368), (4, 128), (1, 384)]
    (codeMat 84) (codeMat 234) (codeMat 461) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

theorem plane456GenSource0233 :
    QuotientRankAtLeast (spanCodes [258, 128, 64, 32, 18, 10, 6, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(258, 197), (128, 3), (64, 2), (32, 40), (18, 216), (10, 208), (6, 384), (1, 128)]
    (codeMat 84) (codeMat 286) (codeMat 303) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

theorem plane456GenSource0234 :
    QuotientRankAtLeast (spanCodes [256, 128, 66, 32, 18, 10, 6, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(256, 1), (128, 3), (66, 198), (32, 8), (18, 216), (10, 240), (6, 128), (1, 384)]
    (codeMat 84) (codeMat 94) (codeMat 500) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

theorem plane456GenSource0235 :
    QuotientRankAtLeast (spanCodes [257, 129, 64, 32, 17, 8, 5, 2]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(257, 69), (129, 70), (64, 1), (32, 40), (17, 112), (8, 8), (5, 256), (2, 384)]
    (codeMat 84) (codeMat 405) (codeMat 407) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

theorem plane456GenSource0236 :
    QuotientRankAtLeast (spanCodes [256, 129, 65, 32, 17, 8, 5, 2]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(256, 1), (129, 326), (65, 325), (32, 8), (17, 368), (8, 40), (5, 256), (2, 384)]
    (codeMat 84) (codeMat 213) (codeMat 470) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

theorem plane456GenSource0237 :
    QuotientRankAtLeast (spanCodes [257, 129, 64, 32, 16, 9, 4, 3]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(257, 196), (129, 197), (64, 3), (32, 32), (16, 40), (9, 216), (4, 256), (3, 384)]
    (codeMat 84) (codeMat 395) (codeMat 474) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

theorem plane456GenSource0238 :
    QuotientRankAtLeast (spanCodes [257, 129, 64, 32, 17, 9, 5, 3]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(257, 197), (129, 199), (64, 3), (32, 40), (17, 248), (9, 216), (5, 384), (3, 256)]
    (codeMat 84) (codeMat 415) (codeMat 253) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

theorem plane456GenSource0239 :
    QuotientRankAtLeast (spanCodes [256, 128, 65, 33, 16, 9, 4, 3]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(256, 2), (128, 1), (65, 455), (33, 464), (16, 8), (9, 504), (4, 128), (3, 384)]
    (codeMat 84) (codeMat 107) (codeMat 428) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

end QiushiMatmul
