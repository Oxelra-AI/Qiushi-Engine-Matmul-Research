import QiushiPlane484GenData
import QiushiCertifiedTransport
import QiushiFlattenSeeds
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane484GenSource1630 :
    QuotientRankAtLeast (spanCodes [256, 129, 64, 33, 17, 8, 4, 2]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(256, 2), (129, 70), (64, 1), (33, 80), (17, 112), (8, 8), (4, 128), (2, 384)]
    (codeMat 84) (codeMat 177) (codeMat 417) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

theorem plane484GenSource1631 :
    QuotientRankAtLeast (spanCodes [257, 128, 64, 32, 17, 8, 5, 2]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(257, 69), (128, 2), (64, 1), (32, 40), (17, 80), (8, 8), (5, 256), (2, 128)]
    (codeMat 84) (codeMat 277) (codeMat 277) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

theorem plane484GenSource1632 :
    QuotientRankAtLeast (spanCodes [256, 128, 65, 32, 17, 8, 5, 2]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(256, 1), (128, 2), (65, 325), (32, 8), (17, 336), (8, 40), (5, 256), (2, 128)]
    (codeMat 84) (codeMat 85) (codeMat 340) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

theorem plane484GenSource1633 :
    QuotientRankAtLeast (spanCodes [257, 128, 64, 32, 16, 9, 4, 3]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(257, 196), (128, 1), (64, 3), (32, 32), (16, 8), (9, 216), (4, 256), (3, 128)]
    (codeMat 84) (codeMat 267) (codeMat 282) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

theorem plane484GenSource1634 :
    QuotientRankAtLeast (spanCodes [257, 129, 65, 32, 16, 9, 4, 3]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(257, 452), (129, 453), (65, 455), (32, 32), (16, 40), (9, 504), (4, 256), (3, 128)]
    (codeMat 84) (codeMat 459) (codeMat 346) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

theorem plane484GenSource1635 :
    QuotientRankAtLeast (spanCodes [257, 128, 65, 32, 16, 9, 5, 3]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(257, 453), (128, 1), (65, 455), (32, 40), (16, 8), (9, 504), (5, 128), (3, 384)]
    (codeMat 84) (codeMat 335) (codeMat 426) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

theorem plane484GenSource1636 :
    QuotientRankAtLeast (spanCodes [256, 129, 65, 32, 16, 9, 5, 3]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(256, 1), (129, 453), (65, 455), (32, 8), (16, 40), (9, 504), (5, 384), (3, 128)]
    (codeMat 84) (codeMat 207) (codeMat 370) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

theorem plane484GenSource1637 :
    QuotientRankAtLeast (spanCodes [257, 128, 64, 33, 16, 9, 5, 3]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(257, 199), (128, 1), (64, 3), (33, 248), (16, 8), (9, 216), (5, 256), (3, 128)]
    (codeMat 84) (codeMat 303) (codeMat 286) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

theorem plane484GenSource1638 :
    QuotientRankAtLeast (spanCodes [256, 128, 65, 33, 16, 9, 5, 3]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(256, 3), (128, 1), (65, 455), (33, 472), (16, 8), (9, 504), (5, 256), (3, 384)]
    (codeMat 84) (codeMat 111) (codeMat 412) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

theorem plane484GenSource1639 :
    QuotientRankAtLeast (spanCodes [256, 129, 65, 33, 16, 9, 5, 3]) 9 := by
  apply quotientRankAtLeast_weaken (n := 9) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [256, 128, 68, 32, 20, 8, 2, 1] [(256, 3), (129, 453), (65, 455), (33, 472), (16, 40), (9, 504), (5, 256), (3, 128)]
    (codeMat 84) (codeMat 239) (codeMat 351) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.flatSeed_3

end QiushiMatmul
