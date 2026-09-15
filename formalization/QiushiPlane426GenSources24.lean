import QiushiPlane426GenData
import QiushiCertifiedTransport
import QiushiOrbit10FP
import QiushiOrbit11FP
import QiushiOrbit14FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane426GenSource0240 :
    QuotientRankAtLeast (spanCodes [272, 146, 66, 50, 10, 4, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(272, 196), (146, 63), (66, 121), (50, 248), (10, 120), (4, 32), (1, 8)]
    (codeMat 142) (codeMat 403) (codeMat 403) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane426GenSource0241 :
    QuotientRankAtLeast (spanCodes [272, 128, 80, 50, 10, 4, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(272, 30), (128, 3), (80, 28), (50, 232), (10, 224), (4, 384), (1, 256)]
    (codeMat 84) (codeMat 370) (codeMat 207) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane426GenSource0242 :
    QuotientRankAtLeast (spanCodes [272, 128, 82, 48, 10, 4, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(272, 362), (128, 511), (82, 284), (48, 360), (10, 224), (4, 128), (1, 256)]
    (codeMat 94) (codeMat 242) (codeMat 205) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane426GenSource0243 :
    QuotientRankAtLeast (spanCodes [272, 148, 80, 32, 8, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(272, 30), (148, 246), (80, 22), (32, 3), (8, 2), (2, 384), (1, 128)]
    (codeMat 98) (codeMat 188) (codeMat 103) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane426GenSource0244 :
    QuotientRankAtLeast (spanCodes [272, 132, 80, 48, 8, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(272, 508), (132, 224), (80, 148), (48, 3), (8, 2), (2, 256), (1, 128)]
    (codeMat 106) (codeMat 428) (codeMat 107) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane426GenSource0245 :
    QuotientRankAtLeast (spanCodes [256, 134, 68, 34, 16, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 511), (134, 508), (68, 149), (34, 224), (16, 256), (10, 96), (1, 360)]
    (codeMat 157) (codeMat 485) (codeMat 171) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane426GenSource0246 :
    QuotientRankAtLeast (spanCodes [256, 130, 70, 36, 16, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 130), (130, 9), (70, 413), (36, 128), (16, 8), (10, 96), (1, 360)]
    (codeMat 215) (codeMat 99) (codeMat 172) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane426GenSource0247 :
    QuotientRankAtLeast (spanCodes [256, 130, 68, 38, 16, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 511), (130, 1), (68, 149), (38, 392), (16, 8), (10, 96), (1, 360)]
    (codeMat 213) (codeMat 359) (codeMat 174) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane426GenSource0248 :
    QuotientRankAtLeast (spanCodes [256, 128, 70, 38, 16, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(256, 3), (128, 1), (70, 149), (38, 136), (16, 8), (10, 96), (1, 360)]
    (codeMat 212) (codeMat 103) (codeMat 188) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane426GenSource0249 :
    QuotientRankAtLeast (spanCodes [258, 130, 70, 38, 18, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(258, 327), (130, 2), (70, 68), (38, 184), (18, 16), (10, 416), (1, 256)]
    (codeMat 93) (codeMat 372) (codeMat 93) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

end QiushiMatmul
