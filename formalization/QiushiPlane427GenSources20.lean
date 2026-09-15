import QiushiPlane427GenData
import QiushiCertifiedTransport
import QiushiOrbit10FP
import QiushiOrbit11FP
import QiushiOrbit14FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane427GenSource0200 :
    QuotientRankAtLeast (spanCodes [266, 136, 72, 34, 16, 6, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(266, 486), (136, 324), (72, 1), (34, 416), (16, 256), (6, 16), (1, 8)]
    (codeMat 142) (codeMat 417) (codeMat 177) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane427GenSource0201 :
    QuotientRankAtLeast (spanCodes [264, 138, 72, 34, 16, 6, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(264, 326), (138, 484), (72, 3), (34, 416), (16, 256), (6, 16), (1, 24)]
    (codeMat 142) (codeMat 425) (codeMat 249) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane427GenSource0202 :
    QuotientRankAtLeast (spanCodes [384, 66, 34, 16, 8, 6, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(384, 128), (66, 68), (34, 52), (16, 32), (8, 8), (6, 2), (1, 1)]
    (codeMat 273) (codeMat 417) (codeMat 177) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane427GenSource0203 :
    QuotientRankAtLeast (spanCodes [256, 134, 70, 36, 16, 14, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 128), (134, 488), (70, 104), (36, 130), (16, 511), (14, 97), (1, 8)]
    (codeMat 271) (codeMat 179) (codeMat 421) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane427GenSource0204 :
    QuotientRankAtLeast (spanCodes [262, 128, 70, 36, 16, 14, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(262, 488), (128, 128), (70, 104), (36, 511), (16, 130), (14, 105), (1, 8)]
    (codeMat 270) (codeMat 309) (codeMat 309) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane427GenSource0205 :
    QuotientRankAtLeast (spanCodes [260, 128, 68, 36, 16, 14, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(260, 9), (128, 128), (68, 393), (36, 8), (16, 130), (14, 284), (1, 511)]
    (codeMat 286) (codeMat 93) (codeMat 372) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane427GenSource0206 :
    QuotientRankAtLeast (spanCodes [256, 130, 66, 36, 16, 14, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 128), (130, 9), (66, 393), (36, 130), (16, 8), (14, 227), (1, 511)]
    (codeMat 279) (codeMat 107) (codeMat 428) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane427GenSource0207 :
    QuotientRankAtLeast (spanCodes [260, 132, 64, 36, 16, 14, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(260, 1), (132, 385), (64, 128), (36, 8), (16, 511), (14, 276), (1, 130)]
    (codeMat 285) (codeMat 158) (codeMat 358) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane427GenSource0208 :
    QuotientRankAtLeast (spanCodes [258, 130, 64, 36, 16, 14, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(258, 385), (130, 1), (64, 128), (36, 511), (16, 8), (14, 406), (1, 130)]
    (codeMat 277) (codeMat 302) (codeMat 302) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane427GenSource0209 :
    QuotientRankAtLeast (spanCodes [256, 134, 68, 36, 16, 12, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(256, 219), (134, 228), (68, 82), (36, 216), (16, 32), (12, 208), (1, 128)]
    (codeMat 87) (codeMat 172) (codeMat 99) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

end QiushiMatmul
