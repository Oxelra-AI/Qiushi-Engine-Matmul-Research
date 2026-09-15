import QiushiPlane489GenData
import QiushiCertifiedTransport
import QiushiFlattenSeeds
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane489GenSource0350 :
    QuotientRankAtLeast (spanCodes [256, 128, 68, 32, 20, 8, 2, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(256, 1), (128, 2), (68, 68), (32, 8), (20, 80), (8, 32), (2, 128), (1, 256)]
    (codeMat 84) (codeMat 84) (codeMat 84) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

theorem plane489GenSource0351 :
    QuotientRankAtLeast (spanCodes [258, 128, 66, 34, 18, 10, 6, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(258, 199), (128, 3), (66, 198), (34, 248), (18, 216), (10, 240), (6, 256), (1, 384)]
    (codeMat 84) (codeMat 382) (codeMat 499) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

theorem plane489GenSource0352 :
    QuotientRankAtLeast (spanCodes [256, 129, 64, 33, 16, 8, 4, 2]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(256, 2), (129, 68), (64, 1), (33, 80), (16, 32), (8, 8), (4, 128), (2, 256)]
    (codeMat 84) (codeMat 161) (codeMat 161) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

theorem plane489GenSource0353 :
    QuotientRankAtLeast (spanCodes [256, 129, 65, 33, 17, 8, 4, 2]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(256, 2), (129, 326), (65, 325), (33, 336), (17, 368), (8, 40), (4, 128), (2, 384)]
    (codeMat 84) (codeMat 241) (codeMat 489) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

theorem plane489GenSource0354 :
    QuotientRankAtLeast (spanCodes [256, 129, 64, 33, 17, 8, 5, 2]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(256, 3), (129, 70), (64, 1), (33, 88), (17, 112), (8, 8), (5, 128), (2, 384)]
    (codeMat 84) (codeMat 181) (codeMat 423) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

theorem plane489GenSource0355 :
    QuotientRankAtLeast (spanCodes [257, 129, 65, 33, 16, 9, 4, 3]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(257, 454), (129, 453), (65, 455), (33, 496), (16, 40), (9, 504), (4, 384), (3, 128)]
    (codeMat 84) (codeMat 491) (codeMat 375) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

theorem plane489GenSource0356 :
    QuotientRankAtLeast (spanCodes [257, 129, 64, 33, 17, 9, 4, 3]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(257, 198), (129, 199), (64, 3), (33, 240), (17, 248), (9, 216), (4, 384), (3, 256)]
    (codeMat 84) (codeMat 443) (codeMat 254) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

theorem plane489GenSource0357 :
    QuotientRankAtLeast (spanCodes [257, 129, 64, 33, 16, 9, 5, 3]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(257, 199), (129, 197), (64, 3), (33, 248), (16, 40), (9, 216), (5, 256), (3, 384)]
    (codeMat 84) (codeMat 431) (codeMat 477) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

theorem plane489GenSource0358 :
    QuotientRankAtLeast (spanCodes [257, 128, 65, 32, 17, 9, 5, 3]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(257, 453), (128, 3), (65, 455), (32, 40), (17, 472), (9, 504), (5, 128), (3, 256)]
    (codeMat 84) (codeMat 351) (codeMat 239) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

theorem plane489GenSource0359 :
    QuotientRankAtLeast (spanCodes [257, 128, 64, 33, 16, 9, 5, 3]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(257, 199), (128, 1), (64, 3), (33, 248), (16, 8), (9, 216), (5, 256), (3, 128)]
    (codeMat 84) (codeMat 303) (codeMat 286) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

end QiushiMatmul
