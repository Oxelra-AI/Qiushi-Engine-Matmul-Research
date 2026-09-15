import QiushiPlane490GenData
import QiushiCertifiedTransport
import QiushiOrbit10FP
import QiushiOrbit14FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane490GenSource0640 :
    QuotientRankAtLeast (spanCodes [257, 130, 64, 35, 18, 10, 4]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(257, 68), (130, 3), (64, 325), (35, 160), (18, 24), (10, 424), (4, 256)]
    (codeMat 93) (codeMat 339) (codeMat 467) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane490GenSource0641 :
    QuotientRankAtLeast (spanCodes [257, 131, 64, 34, 18, 10, 4]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(257, 68), (131, 326), (64, 325), (34, 416), (18, 432), (10, 424), (4, 256)]
    (codeMat 85) (codeMat 465) (codeMat 465) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane490GenSource0642 :
    QuotientRankAtLeast (spanCodes [257, 129, 65, 33, 18, 10, 4]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(257, 104), (129, 488), (65, 360), (33, 105), (18, 511), (10, 381), (4, 8)]
    (codeMat 270) (codeMat 215) (codeMat 342) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane490GenSource0643 :
    QuotientRankAtLeast (spanCodes [259, 131, 67, 35, 16, 10, 4]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(259, 96), (131, 480), (67, 224), (35, 105), (16, 511), (10, 227), (4, 8)]
    (codeMat 271) (codeMat 159) (codeMat 230) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane490GenSource0644 :
    QuotientRankAtLeast (spanCodes [261, 128, 68, 37, 21, 9, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(261, 483), (128, 360), (68, 252), (37, 227), (21, 235), (9, 511), (3, 130)]
    (codeMat 407) (codeMat 459) (codeMat 346) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane490GenSource0645 :
    QuotientRankAtLeast (spanCodes [261, 128, 65, 32, 21, 9, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(261, 70), (128, 325), (65, 1), (32, 432), (21, 168), (9, 8), (3, 256)]
    (codeMat 93) (codeMat 419) (codeMat 183) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane490GenSource0646 :
    QuotientRankAtLeast (spanCodes [260, 132, 65, 37, 20, 9, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(260, 384), (132, 232), (65, 128), (37, 406), (20, 235), (9, 130), (3, 8)]
    (codeMat 334) (codeMat 314) (codeMat 271) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane490GenSource0647 :
    QuotientRankAtLeast (spanCodes [260, 129, 69, 36, 20, 9, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(260, 2), (129, 363), (69, 150), (36, 128), (20, 136), (9, 384), (3, 360)]
    (codeMat 213) (codeMat 122) (codeMat 460) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane490GenSource0648 :
    QuotientRankAtLeast (spanCodes [260, 128, 68, 36, 20, 9, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(260, 8), (128, 384), (68, 136), (36, 1), (20, 510), (9, 3), (3, 360)]
    (codeMat 299) (codeMat 157) (codeMat 486) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane490GenSource0649 :
    QuotientRankAtLeast (spanCodes [260, 133, 65, 36, 20, 9, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(260, 1), (133, 327), (65, 3), (36, 8), (20, 440), (9, 24), (3, 256)]
    (codeMat 93) (codeMat 159) (codeMat 230) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

end QiushiMatmul
