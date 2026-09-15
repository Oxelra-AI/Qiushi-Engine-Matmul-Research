import QiushiPlane427GenData
import QiushiCertifiedTransport
import QiushiOrbit11FP
import QiushiOrbit14FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane427GenSource0160 :
    QuotientRankAtLeast (spanCodes [260, 128, 70, 36, 16, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(260, 130), (128, 9), (70, 245), (36, 128), (16, 8), (10, 96), (1, 360)]
    (codeMat 214) (codeMat 99) (codeMat 172) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane427GenSource0161 :
    QuotientRankAtLeast (spanCodes [256, 132, 64, 36, 16, 12, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(256, 3), (132, 196), (64, 2), (36, 216), (16, 32), (12, 208), (1, 128)]
    (codeMat 84) (codeMat 172) (codeMat 99) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane427GenSource0162 :
    QuotientRankAtLeast (spanCodes [258, 130, 68, 36, 16, 12, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(258, 381), (130, 130), (68, 97), (36, 360), (16, 128), (12, 104), (1, 8)]
    (codeMat 143) (codeMat 277) (codeMat 277) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane427GenSource0163 :
    QuotientRankAtLeast (spanCodes [260, 132, 68, 36, 16, 12, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(260, 219), (132, 228), (68, 210), (36, 216), (16, 32), (12, 208), (1, 128)]
    (codeMat 86) (codeMat 172) (codeMat 99) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane427GenSource0164 :
    QuotientRankAtLeast (spanCodes [256, 130, 70, 36, 16, 12, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 9), (130, 130), (70, 245), (36, 8), (16, 128), (12, 264), (1, 360)]
    (codeMat 159) (codeMat 85) (codeMat 340) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane427GenSource0165 :
    QuotientRankAtLeast (spanCodes [262, 128, 64, 36, 16, 14, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(262, 385), (128, 1), (64, 2), (36, 511), (16, 8), (14, 406), (1, 130)]
    (codeMat 340) (codeMat 302) (codeMat 302) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane427GenSource0166 :
    QuotientRankAtLeast (spanCodes [256, 134, 64, 36, 16, 14, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 1), (134, 385), (64, 2), (36, 8), (16, 511), (14, 276), (1, 130)]
    (codeMat 348) (codeMat 158) (codeMat 358) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane427GenSource0167 :
    QuotientRankAtLeast (spanCodes [260, 128, 66, 36, 16, 14, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(260, 128), (128, 9), (66, 118), (36, 130), (16, 8), (14, 227), (1, 511)]
    (codeMat 342) (codeMat 107) (codeMat 428) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane427GenSource0168 :
    QuotientRankAtLeast (spanCodes [256, 130, 68, 36, 16, 14, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 9), (130, 128), (68, 118), (36, 8), (16, 130), (14, 284), (1, 511)]
    (codeMat 351) (codeMat 93) (codeMat 372) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane427GenSource0169 :
    QuotientRankAtLeast (spanCodes [258, 130, 70, 36, 16, 14, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(258, 488), (130, 128), (70, 96), (36, 511), (16, 130), (14, 105), (1, 8)]
    (codeMat 335) (codeMat 309) (codeMat 309) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

end QiushiMatmul
