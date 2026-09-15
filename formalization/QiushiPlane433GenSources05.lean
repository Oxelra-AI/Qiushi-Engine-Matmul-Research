import QiushiPlane433GenData
import QiushiCertifiedTransport
import QiushiOrbit10FP
import QiushiOrbit11FP
import QiushiOrbit14FP
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

theorem plane433GenSource0050 :
    QuotientRankAtLeast (spanCodes [258, 130, 66, 34, 16, 6, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(258, 11), (130, 2), (66, 52), (34, 208), (16, 128), (6, 8), (1, 32)]
    (codeMat 141) (codeMat 116) (codeMat 92) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane433GenSource0051 :
    QuotientRankAtLeast (spanCodes [258, 136, 66, 40, 16, 6, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(258, 232), (136, 28), (66, 224), (40, 1), (16, 3), (6, 384), (1, 256)]
    (codeMat 98) (codeMat 342) (codeMat 215) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane433GenSource0052 :
    QuotientRankAtLeast (spanCodes [258, 128, 66, 38, 16, 14, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(258, 71), (128, 1), (66, 68), (38, 440), (16, 8), (14, 416), (1, 256)]
    (codeMat 84) (codeMat 358) (codeMat 158) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane433GenSource0053 :
    QuotientRankAtLeast (spanCodes [256, 132, 100, 16, 8, 2, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(256, 256), (132, 160), (100, 228), (16, 2), (8, 3), (2, 16), (1, 24)]
    (codeMat 266) (codeMat 281) (codeMat 281) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane433GenSource0054 :
    QuotientRankAtLeast (spanCodes [258, 130, 70, 36, 16, 12, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(258, 326), (130, 3), (70, 68), (36, 432), (16, 24), (12, 416), (1, 256)]
    (codeMat 85) (codeMat 370) (codeMat 207) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane433GenSource0055 :
    QuotientRankAtLeast (spanCodes [258, 132, 64, 38, 16, 14, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(258, 198), (132, 197), (64, 130), (38, 240), (16, 40), (14, 208), (1, 128)]
    (codeMat 85) (codeMat 426) (codeMat 335) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane433GenSource0056 :
    QuotientRankAtLeast (spanCodes [258, 132, 70, 32, 16, 14, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 32, 68, 128] [(258, 100), (132, 109), (70, 210), (32, 32), (16, 40), (14, 80), (1, 128)]
    (codeMat 87) (codeMat 394) (codeMat 330) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit11_lb12

theorem plane433GenSource0057 :
    QuotientRankAtLeast (spanCodes [258, 162, 66, 16, 10, 6, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(258, 487), (162, 228), (66, 162), (16, 256), (10, 160), (6, 24), (1, 16)]
    (codeMat 142) (codeMat 428) (codeMat 107) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

theorem plane433GenSource0058 :
    QuotientRankAtLeast (spanCodes [258, 130, 64, 34, 16, 14, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 20, 96, 128, 256] [(258, 257), (130, 1), (64, 128), (34, 105), (16, 8), (14, 276), (1, 130)]
    (codeMat 277) (codeMat 270) (codeMat 298) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit14_lb12

theorem plane433GenSource0059 :
    QuotientRankAtLeast (spanCodes [258, 132, 70, 38, 16, 10, 1]) 12 := by
  apply quotientRankAtLeast_weaken (n := 12) _ (by decide)
  exact quotientRankAtLeast_of_code_transport
    [1, 2, 8, 16, 68, 160, 256] [(258, 71), (132, 70), (70, 324), (38, 440), (16, 432), (10, 160), (1, 256)]
    (codeMat 93) (codeMat 500) (codeMat 94) false
    (by decide) (by decide) (by decide) (by decide)
    QiushiMatmul.orbit10_lb12

end QiushiMatmul
