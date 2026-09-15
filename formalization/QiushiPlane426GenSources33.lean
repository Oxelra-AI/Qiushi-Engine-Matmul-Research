import QiushiPlane426GenData
import QiushiCertifiedTransport
import QiushiFlattenSeeds
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane426GenSource0330 :
    QuotientRankAtLeast (spanCodes [256, 130, 64, 34, 16, 10, 6, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(256, 3), (130, 325), (64, 2), (34, 344), (16, 40), (10, 336), (6, 384), (1, 128)]
    (codeMat 84) (codeMat 174) (codeMat 359) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

theorem plane426GenSource0331 :
    QuotientRankAtLeast (spanCodes [256, 130, 66, 32, 16, 10, 6, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(256, 1), (130, 325), (66, 326), (32, 8), (16, 40), (10, 368), (6, 256), (1, 384)]
    (codeMat 84) (codeMat 206) (codeMat 498) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

theorem plane426GenSource0332 :
    QuotientRankAtLeast (spanCodes [258, 130, 64, 34, 18, 10, 4, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(258, 454), (130, 455), (64, 2), (34, 496), (18, 504), (10, 464), (4, 384), (1, 128)]
    (codeMat 84) (codeMat 442) (codeMat 334) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

theorem plane426GenSource0333 :
    QuotientRankAtLeast (spanCodes [256, 130, 66, 34, 16, 10, 4, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(256, 2), (130, 325), (66, 326), (34, 336), (16, 40), (10, 368), (4, 128), (1, 384)]
    (codeMat 84) (codeMat 234) (codeMat 461) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

theorem plane426GenSource0334 :
    QuotientRankAtLeast (spanCodes [260, 128, 68, 36, 20, 8, 2, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(260, 455), (128, 2), (68, 452), (36, 504), (20, 464), (8, 32), (2, 128), (1, 256)]
    (codeMat 84) (codeMat 372) (codeMat 93) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

theorem plane426GenSource0335 :
    QuotientRankAtLeast (spanCodes [260, 132, 68, 32, 20, 8, 2, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(260, 325), (132, 326), (68, 324), (32, 40), (20, 368), (8, 32), (2, 384), (1, 256)]
    (codeMat 84) (codeMat 468) (codeMat 87) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

theorem plane426GenSource0336 :
    QuotientRankAtLeast (spanCodes [272, 128, 80, 48, 8, 4, 2, 1]) 6 := by
  apply quotientRankAtLeast_weaken (n := 6) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 160, 64, 16, 8, 4, 2, 1] [(272, 176), (128, 16), (80, 168), (48, 256), (8, 320), (4, 6), (2, 2), (1, 5)]
    (codeMat 161) (codeMat 369) (codeMat 377) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_2

theorem plane426GenSource0337 :
    QuotientRankAtLeast (spanCodes [260, 132, 64, 32, 20, 8, 2, 1]) 6 := by
  apply quotientRankAtLeast_weaken (n := 6) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 160, 64, 16, 8, 4, 2, 1] [(260, 18), (132, 420), (64, 73), (32, 16), (20, 160), (8, 8), (2, 256), (1, 64)]
    (codeMat 87) (codeMat 161) (codeMat 161) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_2

theorem plane426GenSource0338 :
    QuotientRankAtLeast (spanCodes [260, 132, 64, 36, 20, 8, 2, 1]) 6 := by
  apply quotientRankAtLeast_weaken (n := 6) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 160, 64, 16, 8, 4, 2, 1] [(260, 438), (132, 420), (64, 9), (36, 432), (20, 416), (8, 8), (2, 256), (1, 64)]
    (codeMat 86) (codeMat 417) (codeMat 177) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_2

theorem plane426GenSource0339 :
    QuotientRankAtLeast (spanCodes [272, 128, 80, 32, 8, 4, 2, 1]) 6 := by
  apply quotientRankAtLeast_weaken (n := 6) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 160, 64, 16, 8, 4, 2, 1] [(272, 160), (128, 16), (80, 168), (32, 256), (8, 320), (4, 4), (2, 2), (1, 5)]
    (codeMat 161) (codeMat 337) (codeMat 337) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_2

end QiushiMatmul
