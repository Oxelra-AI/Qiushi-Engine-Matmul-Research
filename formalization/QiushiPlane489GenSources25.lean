import QiushiPlane489GenData
import QiushiCertifiedTransport
import QiushiOrbit10FP
import QiushiOrbit11FP
import QiushiOrbit14FP
import QiushiOrbit25FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane489GenSource0250 :
    QuotientRankAtLeast (spanCodes [258, 135, 66, 34, 23, 10]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 4, 8, 80, 256] [(258, 350), (135, 269), (66, 343), (34, 344), (23, 264), (10, 336)]
    (codeMat 214) (codeMat 491) (codeMat 375) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit25_lb12

theorem plane489GenSource0251 :
    QuotientRankAtLeast (spanCodes [258, 130, 70, 38, 18, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(258, 327), (130, 2), (70, 68), (38, 184), (18, 16), (10, 416), (1, 256)]
    (codeMat 93) (codeMat 372) (codeMat 93) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane489GenSource0252 :
    QuotientRankAtLeast (spanCodes [258, 130, 66, 36, 20, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(258, 488), (130, 360), (66, 104), (36, 511), (20, 381), (10, 105), (1, 8)]
    (codeMat 270) (codeMat 423) (codeMat 181) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane489GenSource0253 :
    QuotientRankAtLeast (spanCodes [256, 129, 64, 33, 16, 8, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(256, 32), (129, 80), (64, 8), (33, 68), (16, 2), (8, 1), (2, 128)]
    (codeMat 98) (codeMat 273) (codeMat 273) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane489GenSource0254 :
    QuotientRankAtLeast (spanCodes [256, 129, 68, 37, 16, 8, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 511), (129, 406), (68, 227), (37, 259), (16, 128), (8, 256), (2, 130)]
    (codeMat 171) (codeMat 372) (codeMat 93) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane489GenSource0255 :
    QuotientRankAtLeast (spanCodes [256, 133, 69, 33, 17, 8, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 3), (133, 509), (69, 508), (33, 480), (17, 96), (8, 256), (2, 360)]
    (codeMat 156) (codeMat 230) (codeMat 159) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane489GenSource0256 :
    QuotientRankAtLeast (spanCodes [256, 128, 68, 32, 20, 8, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(256, 1), (128, 2), (68, 68), (32, 8), (20, 80), (8, 32), (2, 128)]
    (codeMat 84) (codeMat 84) (codeMat 84) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane489GenSource0257 :
    QuotientRankAtLeast (spanCodes [256, 133, 64, 33, 20, 8, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 256), (133, 118), (64, 128), (33, 406), (20, 227), (8, 130), (2, 511)]
    (codeMat 286) (codeMat 410) (codeMat 331) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane489GenSource0258 :
    QuotientRankAtLeast (spanCodes [256, 133, 69, 36, 20, 8, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 1), (133, 509), (69, 510), (36, 8), (20, 264), (8, 384), (2, 360)]
    (codeMat 156) (codeMat 206) (codeMat 498) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane489GenSource0259 :
    QuotientRankAtLeast (spanCodes [256, 133, 65, 33, 21, 8, 2]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 360), (133, 404), (65, 9), (33, 105), (21, 276), (8, 8), (2, 130)]
    (codeMat 407) (codeMat 277) (codeMat 277) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

end QiushiMatmul
