import QiushiPlane491GenData
import QiushiCertifiedTransport
import QiushiOrbit10FP
import QiushiOrbit11FP
import QiushiOrbit14FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane491GenSource0680 :
    QuotientRankAtLeast (spanCodes [261, 133, 64, 36, 20, 8, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(261, 326), (133, 324), (64, 3), (36, 432), (20, 416), (8, 24), (2, 256)]
    (codeMat 84) (codeMat 425) (codeMat 249) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane491GenSource0681 :
    QuotientRankAtLeast (spanCodes [256, 133, 69, 36, 17, 8, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(256, 3), (133, 324), (69, 326), (36, 24), (17, 160), (8, 432), (2, 256)]
    (codeMat 92) (codeMat 236) (codeMat 123) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane491GenSource0682 :
    QuotientRankAtLeast (spanCodes [264, 128, 64, 33, 17, 5, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(264, 224), (128, 128), (64, 256), (33, 508), (17, 148), (5, 3), (2, 2)]
    (codeMat 305) (codeMat 372) (codeMat 93) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane491GenSource0683 :
    QuotientRankAtLeast (spanCodes [256, 137, 65, 40, 16, 5, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(256, 256), (137, 246), (65, 432), (40, 2), (16, 3), (5, 16), (2, 24)]
    (codeMat 266) (codeMat 346) (codeMat 459) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane491GenSource0684 :
    QuotientRankAtLeast (spanCodes [257, 144, 81, 49, 8, 5, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(257, 259), (144, 8), (81, 393), (49, 362), (8, 511), (5, 3), (2, 1)]
    (codeMat 369) (codeMat 331) (codeMat 410) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane491GenSource0685 :
    QuotientRankAtLeast (spanCodes [273, 128, 81, 33, 8, 5, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(273, 230), (128, 3), (81, 228), (33, 416), (8, 256), (5, 16), (2, 24)]
    (codeMat 140) (codeMat 370) (codeMat 207) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane491GenSource0686 :
    QuotientRankAtLeast (spanCodes [265, 129, 64, 32, 16, 4, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(265, 228), (129, 160), (64, 256), (32, 3), (16, 2), (4, 24), (2, 16)]
    (codeMat 266) (codeMat 116) (codeMat 92) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane491GenSource0687 :
    QuotientRankAtLeast (spanCodes [262, 134, 70, 36, 18, 14, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(262, 100), (134, 109), (70, 82), (36, 32), (18, 40), (14, 208), (1, 128)]
    (codeMat 95) (codeMat 394) (codeMat 330) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane491GenSource0688 :
    QuotientRankAtLeast (spanCodes [262, 130, 64, 32, 20, 12, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(262, 28), (130, 3), (64, 9), (32, 256), (20, 224), (12, 96), (1, 8)]
    (codeMat 141) (codeMat 275) (codeMat 275) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane491GenSource0689 :
    QuotientRankAtLeast (spanCodes [260, 132, 66, 38, 22, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(260, 360), (132, 353), (66, 278), (38, 105), (22, 97), (10, 276), (1, 130)]
    (codeMat 470) (codeMat 396) (codeMat 106) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

end QiushiMatmul
