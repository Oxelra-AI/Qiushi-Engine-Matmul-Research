import QiushiPlane491GenData
import QiushiCertifiedTransport
import QiushiFlattenSeeds
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane491GenSource0700 :
    QuotientRankAtLeast (spanCodes [258, 130, 64, 32, 16, 10, 4, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(258, 324), (130, 325), (64, 2), (32, 32), (16, 40), (10, 336), (4, 256), (1, 128)]
    (codeMat 84) (codeMat 394) (codeMat 330) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

theorem plane491GenSource0701 :
    QuotientRankAtLeast (spanCodes [256, 128, 66, 34, 16, 8, 6, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(256, 3), (128, 1), (66, 68), (34, 88), (16, 8), (8, 32), (6, 128), (1, 256)]
    (codeMat 84) (codeMat 102) (codeMat 156) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

theorem plane491GenSource0702 :
    QuotientRankAtLeast (spanCodes [256, 130, 66, 32, 16, 10, 6, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(256, 1), (130, 325), (66, 326), (32, 8), (16, 40), (10, 368), (6, 256), (1, 384)]
    (codeMat 84) (codeMat 206) (codeMat 498) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

theorem plane491GenSource0703 :
    QuotientRankAtLeast (spanCodes [257, 129, 65, 32, 17, 8, 4, 2]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(257, 324), (129, 326), (65, 325), (32, 32), (17, 368), (8, 40), (4, 256), (2, 384)]
    (codeMat 84) (codeMat 465) (codeMat 465) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

theorem plane491GenSource0704 :
    QuotientRankAtLeast (spanCodes [257, 128, 65, 33, 17, 9, 4, 2]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(257, 454), (128, 2), (65, 455), (33, 496), (17, 464), (9, 504), (4, 384), (2, 128)]
    (codeMat 84) (codeMat 377) (codeMat 369) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

theorem plane491GenSource0705 :
    QuotientRankAtLeast (spanCodes [257, 128, 64, 33, 17, 8, 5, 2]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(257, 71), (128, 2), (64, 1), (33, 120), (17, 80), (8, 8), (5, 384), (2, 128)]
    (codeMat 84) (codeMat 309) (codeMat 309) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

theorem plane491GenSource0706 :
    QuotientRankAtLeast (spanCodes [256, 129, 65, 32, 16, 9, 5, 2]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(256, 1), (129, 452), (65, 455), (32, 8), (16, 32), (9, 504), (5, 384), (2, 256)]
    (codeMat 84) (codeMat 205) (codeMat 242) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

theorem plane491GenSource0707 :
    QuotientRankAtLeast (spanCodes [256, 129, 64, 33, 16, 8, 4, 3]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(256, 2), (129, 69), (64, 1), (33, 80), (16, 40), (8, 8), (4, 128), (3, 256)]
    (codeMat 84) (codeMat 163) (codeMat 165) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

theorem plane491GenSource0708 :
    QuotientRankAtLeast (spanCodes [257, 129, 65, 33, 17, 8, 4, 3]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(257, 326), (129, 327), (65, 325), (33, 368), (17, 376), (8, 40), (4, 384), (3, 128)]
    (codeMat 84) (codeMat 499) (codeMat 382) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

theorem plane491GenSource0709 :
    QuotientRankAtLeast (spanCodes [256, 129, 64, 33, 17, 8, 5, 3]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(256, 3), (129, 71), (64, 1), (33, 88), (17, 120), (8, 8), (5, 128), (3, 384)]
    (codeMat 84) (codeMat 183) (codeMat 419) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

end QiushiMatmul
