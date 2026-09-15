import QiushiPlane484GenData
import QiushiCertifiedTransport
import QiushiOrbit10FP
import QiushiOrbit11FP
import QiushiOrbit14FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane484GenSource1560 :
    QuotientRankAtLeast (spanCodes [256, 129, 64, 34, 19, 10, 4]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 1), (129, 29), (64, 3), (34, 105), (19, 373), (10, 235), (4, 8)]
    (codeMat 396) (codeMat 143) (codeMat 482) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane484GenSource1561 :
    QuotientRankAtLeast (spanCodes [257, 129, 66, 33, 19, 10, 4]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(257, 404), (129, 413), (66, 245), (33, 276), (19, 414), (10, 373), (4, 130)]
    (codeMat 415) (codeMat 122) (codeMat 460) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane484GenSource1562 :
    QuotientRankAtLeast (spanCodes [256, 128, 66, 33, 19, 10, 4]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 1), (128, 3), (66, 29), (33, 97), (19, 235), (10, 373), (4, 8)]
    (codeMat 460) (codeMat 87) (codeMat 468) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane484GenSource1563 :
    QuotientRankAtLeast (spanCodes [257, 131, 64, 33, 19, 10, 4]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(257, 96), (131, 232), (64, 360), (33, 97), (19, 235), (10, 373), (4, 8)]
    (codeMat 334) (codeMat 87) (codeMat 468) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane484GenSource1564 :
    QuotientRankAtLeast (spanCodes [256, 130, 64, 33, 19, 10, 4]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 128), (130, 3), (64, 384), (33, 276), (19, 414), (10, 373), (4, 130)]
    (codeMat 285) (codeMat 122) (codeMat 460) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane484GenSource1565 :
    QuotientRankAtLeast (spanCodes [256, 133, 68, 37, 16, 9, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 511), (133, 373), (68, 284), (37, 480), (16, 360), (9, 256), (3, 8)]
    (codeMat 206) (codeMat 486) (codeMat 157) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane484GenSource1566 :
    QuotientRankAtLeast (spanCodes [257, 128, 64, 37, 16, 9, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(257, 70), (128, 3), (64, 1), (37, 112), (16, 216), (9, 8), (3, 128)]
    (codeMat 92) (codeMat 307) (codeMat 311) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane484GenSource1567 :
    QuotientRankAtLeast (spanCodes [260, 133, 65, 36, 16, 9, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(260, 1), (133, 326), (65, 2), (36, 8), (16, 432), (9, 16), (3, 256)]
    (codeMat 93) (codeMat 156) (codeMat 102) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane484GenSource1568 :
    QuotientRankAtLeast (spanCodes [256, 128, 69, 33, 16, 9, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 384), (128, 128), (69, 392), (33, 510), (16, 2), (9, 511), (3, 360)]
    (codeMat 298) (codeMat 377) (codeMat 369) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane484GenSource1569 :
    QuotientRankAtLeast (spanCodes [261, 129, 65, 33, 16, 9, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(261, 198), (129, 129), (65, 3), (33, 240), (16, 8), (9, 216), (3, 128)]
    (codeMat 85) (codeMat 299) (codeMat 318) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

end QiushiMatmul
