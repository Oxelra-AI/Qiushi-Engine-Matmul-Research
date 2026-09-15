import QiushiPlane484GenData
import QiushiCertifiedTransport
import QiushiFlattenSeeds
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane484GenSource1660 :
    QuotientRankAtLeast (spanCodes [258, 128, 64, 34, 18, 10, 6, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(258, 199), (128, 3), (64, 2), (34, 248), (18, 216), (10, 208), (6, 256), (1, 128)]
    (codeMat 84) (codeMat 318) (codeMat 299) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

theorem plane484GenSource1661 :
    QuotientRankAtLeast (spanCodes [256, 130, 66, 34, 18, 10, 4, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(256, 2), (130, 455), (66, 454), (34, 464), (18, 504), (10, 496), (4, 128), (1, 384)]
    (codeMat 84) (codeMat 250) (codeMat 397) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

theorem plane484GenSource1662 :
    QuotientRankAtLeast (spanCodes [258, 130, 64, 34, 18, 10, 4, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(258, 454), (130, 455), (64, 2), (34, 496), (18, 504), (10, 464), (4, 384), (1, 128)]
    (codeMat 84) (codeMat 442) (codeMat 334) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

theorem plane484GenSource1663 :
    QuotientRankAtLeast (spanCodes [258, 130, 66, 32, 18, 10, 4, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(258, 452), (130, 455), (66, 454), (32, 32), (18, 504), (10, 496), (4, 256), (1, 384)]
    (codeMat 84) (codeMat 474) (codeMat 395) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

theorem plane484GenSource1664 :
    QuotientRankAtLeast (spanCodes [258, 128, 64, 32, 18, 10, 4, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(258, 196), (128, 3), (64, 2), (32, 32), (18, 216), (10, 208), (4, 256), (1, 128)]
    (codeMat 84) (codeMat 282) (codeMat 267) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

end QiushiMatmul
