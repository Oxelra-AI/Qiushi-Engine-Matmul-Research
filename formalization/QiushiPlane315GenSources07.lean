import QiushiPlane315GenData
import QiushiCertifiedTransport
import QiushiFlattenSeeds
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane315GenSource0070 :
    QuotientRankAtLeast (spanCodes [258, 130, 66, 34, 16, 10, 6, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(258, 327), (130, 325), (66, 326), (34, 376), (16, 40), (10, 368), (6, 128), (1, 384)]
    (codeMat 84) (codeMat 494) (codeMat 501) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

theorem plane315GenSource0071 :
    QuotientRankAtLeast (spanCodes [256, 130, 66, 34, 18, 10, 4, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(256, 2), (130, 455), (66, 454), (34, 464), (18, 504), (10, 496), (4, 128), (1, 384)]
    (codeMat 84) (codeMat 250) (codeMat 397) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

theorem plane315GenSource0072 :
    QuotientRankAtLeast (spanCodes [260, 132, 68, 36, 20, 8, 2, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(260, 455), (132, 454), (68, 452), (36, 504), (20, 496), (8, 32), (2, 384), (1, 256)]
    (codeMat 84) (codeMat 500) (codeMat 94) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

theorem plane315GenSource0073 :
    QuotientRankAtLeast (spanCodes [260, 128, 64, 32, 16, 8, 2, 1]) 3 := by
  apply quotientRankAtLeast_weaken (n := 3) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [128, 64, 32, 16, 8, 4, 2, 1] [(260, 4), (128, 65), (64, 130), (32, 32), (16, 8), (8, 16), (2, 64), (1, 128)]
    (codeMat 85) (codeMat 266) (codeMat 266) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_1

end QiushiMatmul
