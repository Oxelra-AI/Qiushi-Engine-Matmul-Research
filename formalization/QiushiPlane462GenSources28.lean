import QiushiPlane462GenData
import QiushiCertifiedTransport
import QiushiFlattenSeeds
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane462GenSource0280 :
    QuotientRankAtLeast (spanCodes [256, 128, 65, 32, 17, 9, 5, 3]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(256, 1), (128, 3), (65, 455), (32, 8), (17, 472), (9, 504), (5, 384), (3, 256)]
    (codeMat 84) (codeMat 95) (codeMat 244) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

theorem plane462GenSource0281 :
    QuotientRankAtLeast (spanCodes [256, 128, 65, 33, 16, 9, 5, 3]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(256, 3), (128, 1), (65, 455), (33, 472), (16, 8), (9, 504), (5, 256), (3, 384)]
    (codeMat 84) (codeMat 111) (codeMat 412) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

theorem plane462GenSource0282 :
    QuotientRankAtLeast (spanCodes [256, 129, 64, 33, 17, 9, 4, 3]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(256, 2), (129, 199), (64, 3), (33, 208), (17, 248), (9, 216), (4, 128), (3, 256)]
    (codeMat 84) (codeMat 187) (codeMat 229) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

theorem plane462GenSource0283 :
    QuotientRankAtLeast (spanCodes [257, 128, 64, 33, 16, 9, 4, 3]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(257, 198), (128, 1), (64, 3), (33, 240), (16, 8), (9, 216), (4, 384), (3, 128)]
    (codeMat 84) (codeMat 299) (codeMat 318) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

theorem plane462GenSource0284 :
    QuotientRankAtLeast (spanCodes [256, 128, 65, 33, 17, 8, 5, 2]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(256, 3), (128, 2), (65, 325), (33, 344), (17, 336), (8, 40), (5, 384), (2, 128)]
    (codeMat 84) (codeMat 117) (codeMat 380) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

theorem plane462GenSource0285 :
    QuotientRankAtLeast (spanCodes [257, 129, 65, 33, 16, 8, 5, 2]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(257, 327), (129, 324), (65, 325), (33, 376), (16, 32), (8, 40), (5, 128), (2, 256)]
    (codeMat 84) (codeMat 485) (codeMat 171) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

theorem plane462GenSource0286 :
    QuotientRankAtLeast (spanCodes [257, 128, 64, 33, 17, 8, 4, 2]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(257, 70), (128, 2), (64, 1), (33, 112), (17, 80), (8, 8), (4, 384), (2, 128)]
    (codeMat 84) (codeMat 305) (codeMat 305) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

theorem plane462GenSource0287 :
    QuotientRankAtLeast (spanCodes [256, 129, 64, 33, 16, 8, 4, 2]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(256, 2), (129, 68), (64, 1), (33, 80), (16, 32), (8, 8), (4, 128), (2, 256)]
    (codeMat 84) (codeMat 161) (codeMat 161) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

theorem plane462GenSource0288 :
    QuotientRankAtLeast (spanCodes [256, 130, 66, 34, 18, 10, 6, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(256, 3), (130, 455), (66, 454), (34, 472), (18, 504), (10, 496), (6, 256), (1, 384)]
    (codeMat 84) (codeMat 254) (codeMat 443) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

theorem plane462GenSource0289 :
    QuotientRankAtLeast (spanCodes [256, 130, 66, 32, 16, 10, 6, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(256, 1), (130, 325), (66, 326), (32, 8), (16, 40), (10, 368), (6, 256), (1, 384)]
    (codeMat 84) (codeMat 206) (codeMat 498) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

end QiushiMatmul
