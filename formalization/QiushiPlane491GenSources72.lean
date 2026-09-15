import QiushiPlane491GenData
import QiushiCertifiedTransport
import QiushiFlattenSeeds
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane491GenSource0720 :
    QuotientRankAtLeast (spanCodes [258, 128, 66, 34, 16, 8, 6, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(258, 71), (128, 1), (66, 68), (34, 120), (16, 8), (8, 32), (6, 384), (1, 256)]
    (codeMat 84) (codeMat 358) (codeMat 158) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

theorem plane491GenSource0721 :
    QuotientRankAtLeast (spanCodes [256, 128, 66, 34, 18, 10, 4, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(256, 2), (128, 3), (66, 198), (34, 208), (18, 216), (10, 240), (4, 128), (1, 384)]
    (codeMat 84) (codeMat 122) (codeMat 460) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

theorem plane491GenSource0722 :
    QuotientRankAtLeast (spanCodes [258, 128, 64, 34, 16, 10, 4, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(258, 70), (128, 1), (64, 2), (34, 112), (16, 8), (10, 80), (4, 384), (1, 128)]
    (codeMat 84) (codeMat 298) (codeMat 270) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

theorem plane491GenSource0723 :
    QuotientRankAtLeast (spanCodes [258, 128, 66, 34, 18, 8, 4, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(258, 198), (128, 3), (66, 196), (34, 240), (18, 216), (8, 32), (4, 384), (1, 256)]
    (codeMat 84) (codeMat 370) (codeMat 207) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

theorem plane491GenSource0724 :
    QuotientRankAtLeast (spanCodes [256, 132, 64, 36, 20, 12, 2, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(256, 3), (132, 198), (64, 2), (36, 216), (20, 240), (12, 208), (2, 384), (1, 128)]
    (codeMat 84) (codeMat 188) (codeMat 103) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

theorem plane491GenSource0725 :
    QuotientRankAtLeast (spanCodes [260, 132, 68, 36, 16, 12, 2, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(260, 455), (132, 452), (68, 454), (36, 504), (16, 32), (12, 496), (2, 256), (1, 384)]
    (codeMat 84) (codeMat 492) (codeMat 115) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

end QiushiMatmul
