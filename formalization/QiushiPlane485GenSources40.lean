import QiushiPlane485GenData
import QiushiCertifiedTransport
import QiushiFlattenSeeds
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane485GenSource0400 :
    QuotientRankAtLeast (spanCodes [256, 128, 66, 32, 18, 10, 6, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(256, 1), (128, 3), (66, 198), (32, 8), (18, 216), (10, 240), (6, 128), (1, 384)]
    (codeMat 84) (codeMat 94) (codeMat 500) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

theorem plane485GenSource0401 :
    QuotientRankAtLeast (spanCodes [258, 128, 66, 34, 18, 10, 6, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(258, 199), (128, 3), (66, 198), (34, 248), (18, 216), (10, 240), (6, 256), (1, 384)]
    (codeMat 84) (codeMat 382) (codeMat 499) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

theorem plane485GenSource0402 :
    QuotientRankAtLeast (spanCodes [256, 130, 66, 34, 18, 10, 6, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(256, 3), (130, 455), (66, 454), (34, 472), (18, 504), (10, 496), (6, 256), (1, 384)]
    (codeMat 84) (codeMat 254) (codeMat 443) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

theorem plane485GenSource0403 :
    QuotientRankAtLeast (spanCodes [256, 129, 64, 33, 16, 8, 4, 2]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(256, 2), (129, 68), (64, 1), (33, 80), (16, 32), (8, 8), (4, 128), (2, 256)]
    (codeMat 84) (codeMat 161) (codeMat 161) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

theorem plane485GenSource0404 :
    QuotientRankAtLeast (spanCodes [257, 129, 65, 33, 16, 8, 4, 2]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(257, 326), (129, 324), (65, 325), (33, 368), (16, 32), (8, 40), (4, 384), (2, 256)]
    (codeMat 84) (codeMat 481) (codeMat 185) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

theorem plane485GenSource0405 :
    QuotientRankAtLeast (spanCodes [257, 128, 64, 32, 17, 8, 5, 2]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(257, 69), (128, 2), (64, 1), (32, 40), (17, 80), (8, 8), (5, 256), (2, 128)]
    (codeMat 84) (codeMat 277) (codeMat 277) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

theorem plane485GenSource0406 :
    QuotientRankAtLeast (spanCodes [257, 129, 64, 32, 17, 9, 5, 3]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(257, 197), (129, 199), (64, 3), (32, 40), (17, 248), (9, 216), (5, 384), (3, 256)]
    (codeMat 84) (codeMat 415) (codeMat 253) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

theorem plane485GenSource0407 :
    QuotientRankAtLeast (spanCodes [257, 128, 65, 32, 17, 9, 5, 3]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(257, 453), (128, 3), (65, 455), (32, 40), (17, 472), (9, 504), (5, 128), (3, 256)]
    (codeMat 84) (codeMat 351) (codeMat 239) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

theorem plane485GenSource0408 :
    QuotientRankAtLeast (spanCodes [256, 128, 65, 32, 17, 9, 5, 3]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(256, 1), (128, 3), (65, 455), (32, 8), (17, 472), (9, 504), (5, 384), (3, 256)]
    (codeMat 84) (codeMat 95) (codeMat 244) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

theorem plane485GenSource0409 :
    QuotientRankAtLeast (spanCodes [256, 129, 64, 32, 17, 9, 5, 3]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(256, 1), (129, 199), (64, 3), (32, 8), (17, 248), (9, 216), (5, 128), (3, 256)]
    (codeMat 84) (codeMat 159) (codeMat 230) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

end QiushiMatmul
