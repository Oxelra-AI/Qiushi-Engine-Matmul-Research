import QiushiPlane462GenData
import QiushiCertifiedTransport
import QiushiFlattenSeeds
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane462GenSource0270 :
    QuotientRankAtLeast (spanCodes [258, 128, 64, 34, 16, 10, 4, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(258, 70), (128, 1), (64, 2), (34, 112), (16, 8), (10, 80), (4, 384), (1, 128)]
    (codeMat 84) (codeMat 298) (codeMat 270) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

theorem plane462GenSource0271 :
    QuotientRankAtLeast (spanCodes [258, 128, 64, 32, 18, 10, 4, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(258, 196), (128, 3), (64, 2), (32, 32), (18, 216), (10, 208), (4, 256), (1, 128)]
    (codeMat 84) (codeMat 282) (codeMat 267) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

theorem plane462GenSource0272 :
    QuotientRankAtLeast (spanCodes [256, 128, 66, 34, 16, 10, 6, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(256, 3), (128, 1), (66, 70), (34, 88), (16, 8), (10, 112), (6, 128), (1, 384)]
    (codeMat 84) (codeMat 110) (codeMat 444) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

theorem plane462GenSource0273 :
    QuotientRankAtLeast (spanCodes [256, 128, 66, 32, 18, 10, 6, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(256, 1), (128, 3), (66, 198), (32, 8), (18, 216), (10, 240), (6, 128), (1, 384)]
    (codeMat 84) (codeMat 94) (codeMat 500) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

theorem plane462GenSource0274 :
    QuotientRankAtLeast (spanCodes [257, 129, 64, 32, 17, 8, 4, 2]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(257, 68), (129, 70), (64, 1), (32, 32), (17, 112), (8, 8), (4, 256), (2, 384)]
    (codeMat 84) (codeMat 401) (codeMat 401) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

theorem plane462GenSource0275 :
    QuotientRankAtLeast (spanCodes [256, 129, 65, 32, 17, 8, 5, 2]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(256, 1), (129, 326), (65, 325), (32, 8), (17, 368), (8, 40), (5, 256), (2, 384)]
    (codeMat 84) (codeMat 213) (codeMat 470) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

theorem plane462GenSource0276 :
    QuotientRankAtLeast (spanCodes [257, 129, 64, 32, 16, 9, 4, 3]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(257, 196), (129, 197), (64, 3), (32, 32), (16, 40), (9, 216), (4, 256), (3, 384)]
    (codeMat 84) (codeMat 395) (codeMat 474) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

theorem plane462GenSource0277 :
    QuotientRankAtLeast (spanCodes [257, 129, 64, 33, 17, 9, 4, 3]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(257, 198), (129, 199), (64, 3), (33, 240), (17, 248), (9, 216), (4, 384), (3, 256)]
    (codeMat 84) (codeMat 443) (codeMat 254) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

theorem plane462GenSource0278 :
    QuotientRankAtLeast (spanCodes [256, 129, 65, 32, 16, 9, 5, 3]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(256, 1), (129, 453), (65, 455), (32, 8), (16, 40), (9, 504), (5, 384), (3, 128)]
    (codeMat 84) (codeMat 207) (codeMat 370) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

theorem plane462GenSource0279 :
    QuotientRankAtLeast (spanCodes [257, 128, 65, 32, 17, 9, 5, 3]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(257, 453), (128, 3), (65, 455), (32, 40), (17, 472), (9, 504), (5, 128), (3, 256)]
    (codeMat 84) (codeMat 351) (codeMat 239) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

end QiushiMatmul
