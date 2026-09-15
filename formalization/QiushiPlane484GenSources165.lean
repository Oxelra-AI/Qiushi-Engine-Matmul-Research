import QiushiPlane484GenData
import QiushiCertifiedTransport
import QiushiFlattenSeeds
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane484GenSource1650 :
    QuotientRankAtLeast (spanCodes [256, 128, 65, 33, 17, 8, 5, 2]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(256, 3), (128, 2), (65, 325), (33, 344), (17, 336), (8, 40), (5, 384), (2, 128)]
    (codeMat 84) (codeMat 117) (codeMat 380) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

theorem plane484GenSource1651 :
    QuotientRankAtLeast (spanCodes [256, 129, 64, 33, 17, 8, 5, 2]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(256, 3), (129, 70), (64, 1), (33, 88), (17, 112), (8, 8), (5, 128), (2, 384)]
    (codeMat 84) (codeMat 181) (codeMat 423) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

theorem plane484GenSource1652 :
    QuotientRankAtLeast (spanCodes [257, 128, 64, 33, 17, 8, 5, 2]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(257, 71), (128, 2), (64, 1), (33, 120), (17, 80), (8, 8), (5, 384), (2, 128)]
    (codeMat 84) (codeMat 309) (codeMat 309) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

theorem plane484GenSource1653 :
    QuotientRankAtLeast (spanCodes [256, 129, 65, 32, 17, 8, 5, 2]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(256, 1), (129, 326), (65, 325), (32, 8), (17, 368), (8, 40), (5, 256), (2, 384)]
    (codeMat 84) (codeMat 213) (codeMat 470) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

theorem plane484GenSource1654 :
    QuotientRankAtLeast (spanCodes [257, 129, 64, 32, 17, 8, 5, 2]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(257, 69), (129, 70), (64, 1), (32, 40), (17, 112), (8, 8), (5, 256), (2, 384)]
    (codeMat 84) (codeMat 405) (codeMat 407) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

theorem plane484GenSource1655 :
    QuotientRankAtLeast (spanCodes [256, 129, 65, 33, 17, 8, 4, 2]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(256, 2), (129, 326), (65, 325), (33, 336), (17, 368), (8, 40), (4, 128), (2, 384)]
    (codeMat 84) (codeMat 241) (codeMat 489) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

theorem plane484GenSource1656 :
    QuotientRankAtLeast (spanCodes [257, 128, 65, 33, 17, 8, 4, 2]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(257, 326), (128, 2), (65, 325), (33, 368), (17, 336), (8, 40), (4, 384), (2, 128)]
    (codeMat 84) (codeMat 369) (codeMat 377) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

theorem plane484GenSource1657 :
    QuotientRankAtLeast (spanCodes [257, 129, 65, 32, 17, 8, 4, 2]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(257, 324), (129, 326), (65, 325), (32, 32), (17, 368), (8, 40), (4, 256), (2, 384)]
    (codeMat 84) (codeMat 465) (codeMat 465) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

theorem plane484GenSource1658 :
    QuotientRankAtLeast (spanCodes [257, 128, 64, 32, 17, 8, 4, 2]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(257, 68), (128, 2), (64, 1), (32, 32), (17, 80), (8, 8), (4, 256), (2, 128)]
    (codeMat 84) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

theorem plane484GenSource1659 :
    QuotientRankAtLeast (spanCodes [256, 130, 64, 34, 18, 10, 6, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(256, 3), (130, 455), (64, 2), (34, 472), (18, 504), (10, 464), (6, 256), (1, 128)]
    (codeMat 84) (codeMat 190) (codeMat 355) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

end QiushiMatmul
