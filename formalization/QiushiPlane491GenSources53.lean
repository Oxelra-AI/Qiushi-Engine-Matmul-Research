import QiushiPlane491GenData
import QiushiCertifiedTransport
import QiushiOrbit10FP
import QiushiOrbit11FP
import QiushiOrbit14FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane491GenSource0530 :
    QuotientRankAtLeast (spanCodes [260, 132, 68, 38, 16, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(260, 325), (132, 326), (68, 324), (38, 424), (16, 432), (10, 160), (1, 256)]
    (codeMat 92) (codeMat 468) (codeMat 87) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane491GenSource0531 :
    QuotientRankAtLeast (spanCodes [256, 134, 68, 36, 16, 12, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(256, 219), (134, 228), (68, 82), (36, 216), (16, 32), (12, 208), (1, 128)]
    (codeMat 87) (codeMat 172) (codeMat 99) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane491GenSource0532 :
    QuotientRankAtLeast (spanCodes [260, 134, 64, 36, 20, 12, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(260, 3), (134, 198), (64, 130), (36, 216), (20, 240), (12, 208), (1, 128)]
    (codeMat 85) (codeMat 188) (codeMat 103) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane491GenSource0533 :
    QuotientRankAtLeast (spanCodes [258, 130, 66, 32, 22, 12, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(258, 326), (130, 325), (66, 324), (32, 432), (22, 424), (12, 160), (1, 256)]
    (codeMat 92) (codeMat 482) (codeMat 143) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane491GenSource0534 :
    QuotientRankAtLeast (spanCodes [262, 134, 64, 36, 20, 14, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(262, 196), (134, 199), (64, 2), (36, 32), (20, 248), (14, 80), (1, 128)]
    (codeMat 92) (codeMat 410) (codeMat 331) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane491GenSource0535 :
    QuotientRankAtLeast (spanCodes [261, 133, 69, 36, 17, 8, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(261, 480), (133, 96), (69, 224), (36, 3), (17, 149), (8, 511), (2, 360)]
    (codeMat 299) (codeMat 239) (codeMat 351) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane491GenSource0536 :
    QuotientRankAtLeast (spanCodes [256, 132, 65, 37, 21, 8, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(256, 325), (132, 68), (65, 3), (37, 424), (21, 416), (8, 24), (2, 256)]
    (codeMat 85) (codeMat 397) (codeMat 250) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane491GenSource0537 :
    QuotientRankAtLeast (spanCodes [256, 133, 64, 37, 20, 8, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 3), (133, 148), (64, 1), (37, 138), (20, 235), (8, 8), (3, 511)]
    (codeMat 468) (codeMat 181) (codeMat 423) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane491GenSource0538 :
    QuotientRankAtLeast (spanCodes [257, 133, 65, 37, 21, 8, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(257, 139), (133, 119), (65, 130), (37, 136), (21, 392), (8, 128), (3, 360)]
    (codeMat 159) (codeMat 190) (codeMat 355) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane491GenSource0539 :
    QuotientRankAtLeast (spanCodes [256, 128, 68, 32, 16, 9, 3]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(256, 1), (128, 2), (68, 70), (32, 8), (16, 16), (9, 432), (3, 256)]
    (codeMat 84) (codeMat 92) (codeMat 116) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

end QiushiMatmul
