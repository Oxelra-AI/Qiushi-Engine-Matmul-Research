import QiushiPlane152GenData
import QiushiCertifiedTransport
import QiushiFlattenSeeds
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane152GenSource0010 :
    QuotientRankAtLeast (spanCodes [256, 128, 66, 34, 16, 10, 6, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(256, 3), (128, 1), (66, 70), (34, 88), (16, 8), (10, 112), (6, 128), (1, 384)]
    (codeMat 84) (codeMat 110) (codeMat 444) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

theorem plane152GenSource0011 :
    QuotientRankAtLeast (spanCodes [256, 130, 64, 32, 16, 10, 6, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(256, 1), (130, 325), (64, 2), (32, 8), (16, 40), (10, 336), (6, 256), (1, 128)]
    (codeMat 84) (codeMat 142) (codeMat 354) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

theorem plane152GenSource0012 :
    QuotientRankAtLeast (spanCodes [258, 128, 64, 32, 16, 10, 4, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(258, 68), (128, 1), (64, 2), (32, 32), (16, 8), (10, 80), (4, 256), (1, 128)]
    (codeMat 84) (codeMat 266) (codeMat 266) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

theorem plane152GenSource0013 :
    QuotientRankAtLeast (spanCodes [258, 130, 66, 34, 16, 10, 4, 1]) 6 := by
  apply quotientRankAtLeast_weaken (n := 6) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 160, 64, 16, 8, 4, 2, 1] [(258, 420), (130, 18), (66, 493), (34, 160), (16, 16), (10, 168), (4, 256), (1, 320)]
    (codeMat 87) (codeMat 337) (codeMat 337) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_2

theorem plane152GenSource0014 :
    QuotientRankAtLeast (spanCodes [258, 130, 64, 32, 16, 10, 6, 1]) 6 := by
  apply quotientRankAtLeast_weaken (n := 6) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 160, 64, 16, 8, 4, 2, 1] [(258, 66), (130, 3), (64, 260), (32, 16), (16, 24), (10, 224), (6, 64), (1, 256)]
    (codeMat 85) (codeMat 114) (codeMat 204) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_2

theorem plane152GenSource0015 :
    QuotientRankAtLeast (spanCodes [258, 128, 66, 34, 16, 10, 6, 1]) 6 := by
  apply quotientRankAtLeast_weaken (n := 6) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 160, 64, 16, 8, 4, 2, 1] [(258, 182), (128, 18), (66, 173), (34, 176), (16, 16), (10, 168), (6, 256), (1, 320)]
    (codeMat 86) (codeMat 369) (codeMat 377) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_2

end QiushiMatmul
