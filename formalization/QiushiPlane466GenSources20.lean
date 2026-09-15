import QiushiPlane466GenData
import QiushiCertifiedTransport
import QiushiFlattenSeeds
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane466GenSource0200 :
    QuotientRankAtLeast (spanCodes [256, 128, 65, 32, 17, 8, 5, 2]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(256, 1), (128, 2), (65, 325), (32, 8), (17, 336), (8, 40), (5, 256), (2, 128)]
    (codeMat 84) (codeMat 85) (codeMat 340) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

theorem plane466GenSource0201 :
    QuotientRankAtLeast (spanCodes [257, 129, 65, 33, 17, 8, 5, 2]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(257, 327), (129, 326), (65, 325), (33, 376), (17, 368), (8, 40), (5, 128), (2, 384)]
    (codeMat 84) (codeMat 501) (codeMat 494) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

theorem plane466GenSource0202 :
    QuotientRankAtLeast (spanCodes [257, 129, 64, 33, 17, 9, 4, 3]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(257, 198), (129, 199), (64, 3), (33, 240), (17, 248), (9, 216), (4, 384), (3, 256)]
    (codeMat 84) (codeMat 443) (codeMat 254) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

theorem plane466GenSource0203 :
    QuotientRankAtLeast (spanCodes [257, 128, 65, 32, 16, 9, 5, 3]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(257, 453), (128, 1), (65, 455), (32, 40), (16, 8), (9, 504), (5, 128), (3, 384)]
    (codeMat 84) (codeMat 335) (codeMat 426) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

theorem plane466GenSource0204 :
    QuotientRankAtLeast (spanCodes [256, 129, 65, 33, 16, 9, 5, 3]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(256, 3), (129, 453), (65, 455), (33, 472), (16, 40), (9, 504), (5, 256), (3, 128)]
    (codeMat 84) (codeMat 239) (codeMat 351) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

theorem plane466GenSource0205 :
    QuotientRankAtLeast (spanCodes [256, 128, 65, 32, 17, 9, 5, 3]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(256, 1), (128, 3), (65, 455), (32, 8), (17, 472), (9, 504), (5, 384), (3, 256)]
    (codeMat 84) (codeMat 95) (codeMat 244) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

theorem plane466GenSource0206 :
    QuotientRankAtLeast (spanCodes [256, 129, 64, 33, 16, 9, 4, 3]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(256, 2), (129, 197), (64, 3), (33, 208), (16, 40), (9, 216), (4, 128), (3, 384)]
    (codeMat 84) (codeMat 171) (codeMat 485) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

theorem plane466GenSource0207 :
    QuotientRankAtLeast (spanCodes [257, 128, 64, 32, 16, 9, 4, 3]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(257, 196), (128, 1), (64, 3), (32, 32), (16, 8), (9, 216), (4, 256), (3, 128)]
    (codeMat 84) (codeMat 267) (codeMat 282) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

theorem plane466GenSource0208 :
    QuotientRankAtLeast (spanCodes [256, 129, 65, 33, 16, 8, 5, 2]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(256, 3), (129, 324), (65, 325), (33, 344), (16, 32), (8, 40), (5, 384), (2, 256)]
    (codeMat 84) (codeMat 229) (codeMat 187) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

theorem plane466GenSource0209 :
    QuotientRankAtLeast (spanCodes [258, 130, 66, 32, 18, 10, 6, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(258, 453), (130, 455), (66, 454), (32, 40), (18, 504), (10, 496), (6, 128), (1, 384)]
    (codeMat 84) (codeMat 478) (codeMat 445) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

end QiushiMatmul
