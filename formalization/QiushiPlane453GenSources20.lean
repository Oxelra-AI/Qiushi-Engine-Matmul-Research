import QiushiPlane453GenData
import QiushiCertifiedTransport
import QiushiFlattenSeeds
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane453GenSource0200 :
    QuotientRankAtLeast (spanCodes [256, 128, 65, 32, 17, 9, 5, 3]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(256, 1), (128, 3), (65, 455), (32, 8), (17, 472), (9, 504), (5, 384), (3, 256)]
    (codeMat 84) (codeMat 95) (codeMat 244) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

theorem plane453GenSource0201 :
    QuotientRankAtLeast (spanCodes [257, 128, 65, 32, 17, 9, 5, 3]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(257, 453), (128, 3), (65, 455), (32, 40), (17, 472), (9, 504), (5, 128), (3, 256)]
    (codeMat 84) (codeMat 351) (codeMat 239) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

theorem plane453GenSource0202 :
    QuotientRankAtLeast (spanCodes [256, 129, 64, 33, 16, 9, 4, 3]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(256, 2), (129, 197), (64, 3), (33, 208), (16, 40), (9, 216), (4, 128), (3, 384)]
    (codeMat 84) (codeMat 171) (codeMat 485) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

theorem plane453GenSource0203 :
    QuotientRankAtLeast (spanCodes [257, 128, 64, 33, 16, 9, 4, 3]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(257, 198), (128, 1), (64, 3), (33, 240), (16, 8), (9, 216), (4, 384), (3, 128)]
    (codeMat 84) (codeMat 299) (codeMat 318) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

theorem plane453GenSource0204 :
    QuotientRankAtLeast (spanCodes [257, 129, 64, 32, 16, 9, 4, 3]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(257, 196), (129, 197), (64, 3), (32, 32), (16, 40), (9, 216), (4, 256), (3, 384)]
    (codeMat 84) (codeMat 395) (codeMat 474) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

theorem plane453GenSource0205 :
    QuotientRankAtLeast (spanCodes [258, 128, 66, 34, 18, 10, 6, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(258, 199), (128, 3), (66, 198), (34, 248), (18, 216), (10, 240), (6, 256), (1, 384)]
    (codeMat 84) (codeMat 382) (codeMat 499) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

theorem plane453GenSource0206 :
    QuotientRankAtLeast (spanCodes [258, 130, 66, 32, 18, 10, 6, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(258, 453), (130, 455), (66, 454), (32, 40), (18, 504), (10, 496), (6, 128), (1, 384)]
    (codeMat 84) (codeMat 478) (codeMat 445) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

theorem plane453GenSource0207 :
    QuotientRankAtLeast (spanCodes [256, 128, 66, 32, 18, 10, 6, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(256, 1), (128, 3), (66, 198), (32, 8), (18, 216), (10, 240), (6, 128), (1, 384)]
    (codeMat 84) (codeMat 94) (codeMat 500) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

theorem plane453GenSource0208 :
    QuotientRankAtLeast (spanCodes [258, 130, 64, 34, 16, 10, 4, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(258, 326), (130, 325), (64, 2), (34, 368), (16, 40), (10, 336), (4, 384), (1, 128)]
    (codeMat 84) (codeMat 426) (codeMat 335) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

theorem plane453GenSource0209 :
    QuotientRankAtLeast (spanCodes [258, 128, 64, 32, 16, 10, 4, 1]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(258, 68), (128, 1), (64, 2), (32, 32), (16, 8), (10, 80), (4, 256), (1, 128)]
    (codeMat 84) (codeMat 266) (codeMat 266) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

end QiushiMatmul
